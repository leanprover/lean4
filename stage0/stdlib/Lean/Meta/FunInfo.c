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
uint8_t l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_x_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
if (lean_obj_tag(v_x_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 1;
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
}
else
{
if (lean_obj_tag(v_x_15_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; lean_object* v_head_21_; lean_object* v_tail_22_; uint8_t v___x_23_; 
v_head_19_ = lean_ctor_get(v_x_14_, 0);
v_tail_20_ = lean_ctor_get(v_x_14_, 1);
v_head_21_ = lean_ctor_get(v_x_15_, 0);
v_tail_22_ = lean_ctor_get(v_x_15_, 1);
v___x_23_ = lean_level_eq(v_head_19_, v_head_21_);
if (v___x_23_ == 0)
{
return v___x_23_;
}
else
{
v_x_14_ = v_tail_20_;
v_x_15_ = v_tail_22_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_x_14_, v_x_15_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0___boxed(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_x_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_x_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
uint8_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_c_32_; lean_object* v_ls_33_; lean_object* v_maxArgs_x3f_34_; lean_object* v_c_35_; lean_object* v_ls_36_; lean_object* v_maxArgs_x3f_37_; uint8_t v___x_38_; 
v_c_32_ = lean_ctor_get(v_x_30_, 0);
v_ls_33_ = lean_ctor_get(v_x_30_, 1);
v_maxArgs_x3f_34_ = lean_ctor_get(v_x_30_, 2);
v_c_35_ = lean_ctor_get(v_x_31_, 0);
v_ls_36_ = lean_ctor_get(v_x_31_, 1);
v_maxArgs_x3f_37_ = lean_ctor_get(v_x_31_, 2);
v___x_38_ = lean_name_eq(v_c_32_, v_c_35_);
if (v___x_38_ == 0)
{
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_ls_33_, v_ls_36_);
if (v___x_39_ == 0)
{
return v___x_39_;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_maxArgs_x3f_34_, v_maxArgs_x3f_37_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
uint8_t v_res_41_;
v_res_41_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_30_, v_x_31_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_42_, v_x_43_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_x_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
uint64_t l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(uint64_t v_x_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
return v_x_48_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; uint64_t v___x_52_; uint64_t v___x_53_; 
v_head_50_ = lean_ctor_get(v_x_49_, 0);
v_tail_51_ = lean_ctor_get(v_x_49_, 1);
v___x_52_ = l_Lean_Level_hash(v_head_50_);
v___x_53_ = lean_uint64_mix_hash(v_x_48_, v___x_52_);
v_x_48_ = v___x_53_;
v_x_49_ = v_tail_51_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_48_ = stack[0].m_num;
lean_object* v_x_49_ = stack[1].m_obj;
uint64_t v_res_55_;
v_res_55_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v_x_48_, v_x_49_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0___boxed(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint64_t v_x_108__boxed_58_; uint64_t v_res_59_; lean_object* v_r_60_; 
v_x_108__boxed_58_ = lean_unbox_uint64(v_x_56_);
lean_dec_ref(v_x_56_);
v_res_59_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v_x_108__boxed_58_, v_x_57_);
lean_dec(v_x_57_);
v_r_60_ = lean_box_uint64(v_res_59_);
return v_r_60_;
}
}
uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(lean_object* v_x_61_){
_start:
{
lean_object* v_c_62_; lean_object* v_ls_63_; lean_object* v_maxArgs_x3f_64_; uint64_t v___x_65_; uint64_t v___y_67_; 
v_c_62_ = lean_ctor_get(v_x_61_, 0);
v_ls_63_ = lean_ctor_get(v_x_61_, 1);
v_maxArgs_x3f_64_ = lean_ctor_get(v_x_61_, 2);
v___x_65_ = 0ULL;
if (lean_obj_tag(v_c_62_) == 0)
{
uint64_t v___x_79_; 
v___x_79_ = 1723ULL;
v___y_67_ = v___x_79_;
goto v___jp_66_;
}
else
{
uint64_t v_hash_80_; 
v_hash_80_ = lean_ctor_get_uint64(v_c_62_, sizeof(void*)*2);
v___y_67_ = v_hash_80_;
goto v___jp_66_;
}
v___jp_66_:
{
uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; 
v___x_68_ = lean_uint64_mix_hash(v___x_65_, v___y_67_);
v___x_69_ = 7ULL;
v___x_70_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v___x_69_, v_ls_63_);
v___x_71_ = lean_uint64_mix_hash(v___x_68_, v___x_70_);
if (lean_obj_tag(v_maxArgs_x3f_64_) == 0)
{
uint64_t v___x_72_; uint64_t v___x_73_; 
v___x_72_ = 11ULL;
v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; 
v_val_74_ = lean_ctor_get(v_maxArgs_x3f_64_, 0);
v___x_75_ = lean_uint64_of_nat(v_val_74_);
v___x_76_ = 13ULL;
v___x_77_ = lean_uint64_mix_hash(v___x_75_, v___x_76_);
v___x_78_ = lean_uint64_mix_hash(v___x_71_, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
uint64_t v_res_81_;
v_res_81_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_61_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(lean_object* v_x_82_){
_start:
{
uint64_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_82_);
lean_dec_ref(v_x_82_);
v_r_84_ = lean_box_uint64(v_res_83_);
return v_r_84_;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* v_fn_121_, lean_object* v_maxArgs_x3f_122_, lean_object* v_k_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___f_129_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0));
v___x_130_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1));
v___x_131_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0));
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0));
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_135_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_inc(v_maxArgs_x3f_122_);
lean_inc_ref(v_fn_121_);
v___x_136_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_121_, v_maxArgs_x3f_122_, v_a_124_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_197_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_197_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_197_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_197_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_finfo_142_; lean_object* v___y_143_; lean_object* v___x_175_; lean_object* v_cache_176_; lean_object* v_funInfo_177_; lean_object* v___x_178_; 
v___x_175_ = lean_st_ref_get(v_a_125_);
v_cache_176_ = lean_ctor_get(v___x_175_, 1);
lean_inc_ref(v_cache_176_);
lean_dec(v___x_175_);
v_funInfo_177_ = lean_ctor_get(v_cache_176_, 1);
lean_inc_ref(v_funInfo_177_);
lean_dec_ref(v_cache_176_);
lean_inc(v_a_137_);
v___x_178_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_130_, v___x_131_, v_funInfo_177_, v_a_137_);
lean_dec_ref(v_funInfo_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
if (lean_obj_tag(v_fn_121_) == 4)
{
lean_object* v_declName_179_; lean_object* v_us_180_; uint8_t v___x_181_; 
v_declName_179_ = lean_ctor_get(v_fn_121_, 0);
lean_inc(v_declName_179_);
v_us_180_ = lean_ctor_get(v_fn_121_, 1);
lean_inc_n(v_us_180_, 2);
lean_dec_ref_known(v_fn_121_, 2);
v___x_181_ = l_List_any___redArg(v_us_180_, v___f_129_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc(v_declName_179_);
v___x_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_182_, 0, v_declName_179_);
lean_ctor_set(v___x_182_, 1, v_us_180_);
lean_ctor_set(v___x_182_, 2, v_maxArgs_x3f_122_);
v___x_183_ = l_Lean_Meta_realizeValue___redArg(v___x_132_, v___x_133_, v___x_134_, v___x_135_, v_declName_179_, v___x_182_, v_k_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v_finfo_142_ = v_a_184_;
v___y_143_ = v_a_125_;
goto v___jp_141_;
}
else
{
lean_del_object(v___x_139_);
lean_dec(v_a_137_);
return v___x_183_;
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v_us_180_);
lean_dec(v_declName_179_);
lean_dec(v_maxArgs_x3f_122_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_185_ = lean_apply_5(v_k_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_finfo_142_ = v_a_186_;
v___y_143_ = v_a_125_;
goto v___jp_141_;
}
else
{
lean_del_object(v___x_139_);
lean_dec(v_a_137_);
return v___x_185_;
}
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v_maxArgs_x3f_122_);
lean_dec_ref(v_fn_121_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_187_ = lean_apply_5(v_k_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
v_finfo_142_ = v_a_188_;
v___y_143_ = v_a_125_;
goto v___jp_141_;
}
else
{
lean_del_object(v___x_139_);
lean_dec(v_a_137_);
return v___x_187_;
}
}
}
else
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_del_object(v___x_139_);
lean_dec(v_a_137_);
lean_dec_ref(v_k_123_);
lean_dec(v_maxArgs_x3f_122_);
lean_dec_ref(v_fn_121_);
v_val_189_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_178_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v___x_178_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 0);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_val_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
v___jp_141_:
{
lean_object* v___x_144_; lean_object* v_cache_145_; lean_object* v_mctx_146_; lean_object* v_zetaDeltaFVarIds_147_; lean_object* v_postponed_148_; lean_object* v_diag_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_174_; 
v___x_144_ = lean_st_ref_take(v___y_143_);
v_cache_145_ = lean_ctor_get(v___x_144_, 1);
v_mctx_146_ = lean_ctor_get(v___x_144_, 0);
v_zetaDeltaFVarIds_147_ = lean_ctor_get(v___x_144_, 2);
v_postponed_148_ = lean_ctor_get(v___x_144_, 3);
v_diag_149_ = lean_ctor_get(v___x_144_, 4);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_174_ == 0)
{
v___x_151_ = v___x_144_;
v_isShared_152_ = v_isSharedCheck_174_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_diag_149_);
lean_inc(v_postponed_148_);
lean_inc(v_zetaDeltaFVarIds_147_);
lean_inc(v_cache_145_);
lean_inc(v_mctx_146_);
lean_dec(v___x_144_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_174_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_inferType_153_; lean_object* v_funInfo_154_; lean_object* v_synthInstance_155_; lean_object* v_whnf_156_; lean_object* v_defEqTrans_157_; lean_object* v_defEqPerm_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_173_; 
v_inferType_153_ = lean_ctor_get(v_cache_145_, 0);
v_funInfo_154_ = lean_ctor_get(v_cache_145_, 1);
v_synthInstance_155_ = lean_ctor_get(v_cache_145_, 2);
v_whnf_156_ = lean_ctor_get(v_cache_145_, 3);
v_defEqTrans_157_ = lean_ctor_get(v_cache_145_, 4);
v_defEqPerm_158_ = lean_ctor_get(v_cache_145_, 5);
v_isSharedCheck_173_ = !lean_is_exclusive(v_cache_145_);
if (v_isSharedCheck_173_ == 0)
{
v___x_160_ = v_cache_145_;
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_defEqPerm_158_);
lean_inc(v_defEqTrans_157_);
lean_inc(v_whnf_156_);
lean_inc(v_synthInstance_155_);
lean_inc(v_funInfo_154_);
lean_inc(v_inferType_153_);
lean_dec(v_cache_145_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc_ref(v_finfo_142_);
v___x_162_ = l_Lean_PersistentHashMap_insert___redArg(v___x_130_, v___x_131_, v_funInfo_154_, v_a_137_, v_finfo_142_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_inferType_153_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_synthInstance_155_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_whnf_156_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_defEqTrans_157_);
lean_ctor_set(v_reuseFailAlloc_172_, 5, v_defEqPerm_158_);
v___x_164_ = v_reuseFailAlloc_172_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_164_);
v___x_166_ = v___x_151_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_mctx_146_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_zetaDeltaFVarIds_147_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_postponed_148_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_diag_149_);
v___x_166_ = v_reuseFailAlloc_171_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_st_ref_put(v___y_143_, v___x_166_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v_finfo_142_);
v___x_169_ = v___x_139_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_finfo_142_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
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
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_k_123_);
lean_dec(v_maxArgs_x3f_122_);
lean_dec_ref(v_fn_121_);
v_a_198_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_136_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_136_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_121_ = stack[0].m_obj;
lean_object* v_maxArgs_x3f_122_ = stack[1].m_obj;
lean_object* v_k_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_a_126_ = stack[5].m_obj;
lean_object* v_a_127_ = stack[6].m_obj;
lean_object* v_res_206_;
v_res_206_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(v_fn_121_, v_maxArgs_x3f_122_, v_k_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(lean_object* v_fn_207_, lean_object* v_maxArgs_x3f_208_, lean_object* v_k_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(v_fn_207_, v_maxArgs_x3f_208_, v_k_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object* v_e_216_, lean_object* v_deps_217_, lean_object* v_k_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_Expr_hasFVar(v_e_216_);
if (v___x_219_ == 0)
{
lean_dec(v_k_218_);
return v_deps_217_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_apply_1(v_k_218_, v_deps_217_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object* v_e_221_, lean_object* v_deps_222_, lean_object* v_k_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(v_e_221_, v_deps_222_, v_k_223_);
lean_dec_ref(v_e_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* v_00_u03b1_225_, lean_object* v_e_226_, lean_object* v_deps_227_, lean_object* v_k_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Lean_Expr_hasFVar(v_e_226_);
if (v___x_229_ == 0)
{
lean_dec(v_k_228_);
return v_deps_227_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_apply_1(v_k_228_, v_deps_227_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object* v_00_u03b1_231_, lean_object* v_e_232_, lean_object* v_deps_233_, lean_object* v_k_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(v_00_u03b1_231_, v_e_232_, v_deps_233_, v_k_234_);
lean_dec_ref(v_e_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(lean_object* v_xs_236_, lean_object* v_v_237_, lean_object* v_i_238_){
_start:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_array_get_size(v_xs_236_);
v___x_240_ = lean_nat_dec_lt(v_i_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec(v_i_238_);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_fget_borrowed(v_xs_236_, v_i_238_);
v___x_243_ = lean_expr_eqv(v___x_242_, v_v_237_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_i_238_, v___x_244_);
lean_dec(v_i_238_);
v_i_238_ = v___x_245_;
goto _start;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_i_238_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_248_, lean_object* v_v_249_, lean_object* v_i_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_248_, v_v_249_, v_i_250_);
lean_dec_ref(v_v_249_);
lean_dec_ref(v_xs_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object* v_xs_252_, lean_object* v_v_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_252_, v_v_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object* v_xs_256_, lean_object* v_v_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_256_, v_v_257_);
lean_dec_ref(v_v_257_);
lean_dec_ref(v_xs_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* v_xs_259_, lean_object* v_v_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_259_, v_v_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_val_263_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_261_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v___x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_val_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* v_xs_271_, lean_object* v_v_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_xs_271_, v_v_272_);
lean_dec_ref(v_v_272_);
lean_dec_ref(v_xs_271_);
return v_res_273_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(lean_object* v_a_274_, lean_object* v_as_275_, size_t v_i_276_, size_t v_stop_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_eq(v_i_276_, v_stop_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_array_uget_borrowed(v_as_275_, v_i_276_);
v___x_280_ = lean_nat_dec_eq(v_a_274_, v___x_279_);
if (v___x_280_ == 0)
{
size_t v___x_281_; size_t v___x_282_; 
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_add(v_i_276_, v___x_281_);
v_i_276_ = v___x_282_;
goto _start;
}
else
{
return v___x_280_;
}
}
else
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_274_ = stack[0].m_obj;
lean_object* v_as_275_ = stack[1].m_obj;
size_t v_i_276_ = stack[2].m_num;
size_t v_stop_277_ = stack[3].m_num;
uint8_t v_res_285_;
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_274_, v_as_275_, v_i_276_, v_stop_277_);
stack->m_num = v_res_285_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(lean_object* v_a_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_){
_start:
{
size_t v_i_boxed_290_; size_t v_stop_boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_i_boxed_290_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_291_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_286_, v_as_287_, v_i_boxed_290_, v_stop_boxed_291_);
lean_dec_ref(v_as_287_);
lean_dec(v_a_286_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object* v_as_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_get_size(v_as_294_);
v___x_298_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_297_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_295_, v_as_294_, v___x_299_, v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_294_ = stack[0].m_obj;
lean_object* v_a_295_ = stack[1].m_obj;
uint8_t v_res_302_;
v_res_302_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_294_, v_a_295_);
stack->m_num = v_res_302_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object* v_as_303_, lean_object* v_a_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_as_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* v_fvars_307_, lean_object* v_e_308_, lean_object* v_deps_309_){
_start:
{
lean_object* v_d_311_; lean_object* v_b_312_; 
switch(lean_obj_tag(v_e_308_))
{
case 5:
{
lean_object* v_fn_316_; lean_object* v_arg_317_; uint8_t v___x_318_; 
v_fn_316_ = lean_ctor_get(v_e_308_, 0);
v_arg_317_ = lean_ctor_get(v_e_308_, 1);
v___x_318_ = l_Lean_Expr_hasFVar(v_e_308_);
if (v___x_318_ == 0)
{
return v_deps_309_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_307_, v_fn_316_, v_deps_309_);
v_e_308_ = v_arg_317_;
v_deps_309_ = v___x_319_;
goto _start;
}
}
case 7:
{
lean_object* v_binderType_321_; lean_object* v_body_322_; 
v_binderType_321_ = lean_ctor_get(v_e_308_, 1);
v_body_322_ = lean_ctor_get(v_e_308_, 2);
v_d_311_ = v_binderType_321_;
v_b_312_ = v_body_322_;
goto v___jp_310_;
}
case 6:
{
lean_object* v_binderType_323_; lean_object* v_body_324_; 
v_binderType_323_ = lean_ctor_get(v_e_308_, 1);
v_body_324_ = lean_ctor_get(v_e_308_, 2);
v_d_311_ = v_binderType_323_;
v_b_312_ = v_body_324_;
goto v___jp_310_;
}
case 8:
{
lean_object* v_type_325_; lean_object* v_value_326_; lean_object* v_body_327_; uint8_t v___x_328_; 
v_type_325_ = lean_ctor_get(v_e_308_, 1);
v_value_326_ = lean_ctor_get(v_e_308_, 2);
v_body_327_ = lean_ctor_get(v_e_308_, 3);
v___x_328_ = l_Lean_Expr_hasFVar(v_e_308_);
if (v___x_328_ == 0)
{
return v_deps_309_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_307_, v_type_325_, v_deps_309_);
v___x_330_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_307_, v_value_326_, v___x_329_);
v_e_308_ = v_body_327_;
v_deps_309_ = v___x_330_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_332_; 
v_struct_332_ = lean_ctor_get(v_e_308_, 2);
v_e_308_ = v_struct_332_;
goto _start;
}
case 10:
{
lean_object* v_expr_334_; 
v_expr_334_ = lean_ctor_get(v_e_308_, 1);
v_e_308_ = v_expr_334_;
goto _start;
}
case 1:
{
lean_object* v___x_336_; 
v___x_336_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_307_, v_e_308_);
if (lean_obj_tag(v___x_336_) == 0)
{
return v_deps_309_;
}
else
{
lean_object* v_val_337_; uint8_t v___x_338_; 
v_val_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_deps_309_, v_val_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_push(v_deps_309_, v_val_337_);
return v___x_339_;
}
else
{
lean_dec(v_val_337_);
return v_deps_309_;
}
}
}
default: 
{
return v_deps_309_;
}
}
v___jp_310_:
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_Expr_hasFVar(v_e_308_);
if (v___x_313_ == 0)
{
return v_deps_309_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_307_, v_d_311_, v_deps_309_);
v_e_308_ = v_b_312_;
v_deps_309_ = v___x_314_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* v_fvars_340_, lean_object* v_e_341_, lean_object* v_deps_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_340_, v_e_341_, v_deps_342_);
lean_dec_ref(v_e_341_);
lean_dec_ref(v_fvars_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object* v_hi_344_, lean_object* v_pivot_345_, lean_object* v_as_346_, lean_object* v_i_347_, lean_object* v_k_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_nat_dec_lt(v_k_348_, v_hi_344_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_k_348_);
v___x_350_ = lean_array_fswap(v_as_346_, v_i_347_, v_hi_344_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_i_347_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_fget_borrowed(v_as_346_, v_k_348_);
v___x_353_ = lean_nat_dec_lt(v___x_352_, v_pivot_345_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_k_348_, v___x_354_);
lean_dec(v_k_348_);
v_k_348_ = v___x_355_;
goto _start;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_array_fswap(v_as_346_, v_i_347_, v_k_348_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_i_347_, v___x_358_);
lean_dec(v_i_347_);
v___x_360_ = lean_nat_add(v_k_348_, v___x_358_);
lean_dec(v_k_348_);
v_as_346_ = v___x_357_;
v_i_347_ = v___x_359_;
v_k_348_ = v___x_360_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_362_, lean_object* v_pivot_363_, lean_object* v_as_364_, lean_object* v_i_365_, lean_object* v_k_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_362_, v_pivot_363_, v_as_364_, v_i_365_, v_k_366_);
lean_dec(v_pivot_363_);
lean_dec(v_hi_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_n_368_, lean_object* v_as_369_, lean_object* v_lo_370_, lean_object* v_hi_371_){
_start:
{
lean_object* v___y_373_; uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_lt(v_lo_370_, v_hi_371_);
if (v___x_383_ == 0)
{
lean_dec(v_lo_370_);
return v_as_369_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_mid_386_; lean_object* v___y_388_; lean_object* v___y_394_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_384_ = lean_nat_add(v_lo_370_, v_hi_371_);
v___x_385_ = lean_unsigned_to_nat(1u);
v_mid_386_ = lean_nat_shiftr(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_399_ = lean_array_fget_borrowed(v_as_369_, v_mid_386_);
v___x_400_ = lean_array_fget_borrowed(v_as_369_, v_lo_370_);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
v___y_394_ = v_as_369_;
goto v___jp_393_;
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_array_fswap(v_as_369_, v_lo_370_, v_mid_386_);
v___y_394_ = v___x_402_;
goto v___jp_393_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_array_fget_borrowed(v___y_388_, v_mid_386_);
v___x_390_ = lean_array_fget_borrowed(v___y_388_, v_hi_371_);
v___x_391_ = lean_nat_dec_lt(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v_mid_386_);
v___y_373_ = v___y_388_;
goto v___jp_372_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_array_fswap(v___y_388_, v_mid_386_, v_hi_371_);
lean_dec(v_mid_386_);
v___y_373_ = v___x_392_;
goto v___jp_372_;
}
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_array_fget_borrowed(v___y_394_, v_hi_371_);
v___x_396_ = lean_array_fget_borrowed(v___y_394_, v_lo_370_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
v___y_388_ = v___y_394_;
goto v___jp_387_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_array_fswap(v___y_394_, v_lo_370_, v_hi_371_);
v___y_388_ = v___x_398_;
goto v___jp_387_;
}
}
}
v___jp_372_:
{
lean_object* v_pivot_374_; lean_object* v___x_375_; lean_object* v_fst_376_; lean_object* v_snd_377_; uint8_t v___x_378_; 
v_pivot_374_ = lean_array_fget(v___y_373_, v_hi_371_);
lean_inc_n(v_lo_370_, 2);
v___x_375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_371_, v_pivot_374_, v___y_373_, v_lo_370_, v_lo_370_);
lean_dec(v_pivot_374_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_fst_376_);
v_snd_377_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_377_);
lean_dec_ref(v___x_375_);
v___x_378_ = lean_nat_dec_le(v_hi_371_, v_fst_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_368_, v_snd_377_, v_lo_370_, v_fst_376_);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_fst_376_, v___x_380_);
lean_dec(v_fst_376_);
v_as_369_ = v___x_379_;
v_lo_370_ = v___x_381_;
goto _start;
}
else
{
lean_dec(v_fst_376_);
lean_dec(v_lo_370_);
return v_snd_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_n_403_, lean_object* v_as_404_, lean_object* v_lo_405_, lean_object* v_hi_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_403_, v_as_404_, v_lo_405_, v_hi_406_);
lean_dec(v_hi_406_);
lean_dec(v_n_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_410_, lean_object* v_e_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_deps_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0));
v_deps_414_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_410_, v_e_411_, v___x_413_);
v___x_415_ = lean_array_get_size(v_deps_414_);
v___x_416_ = lean_nat_dec_eq(v___x_415_, v___x_412_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___y_420_; uint8_t v___x_424_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_sub(v___x_415_, v___x_417_);
v___x_424_ = lean_nat_dec_le(v___x_412_, v___x_418_);
if (v___x_424_ == 0)
{
lean_inc(v___x_418_);
v___y_420_ = v___x_418_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___x_412_;
goto v___jp_419_;
}
v___jp_419_:
{
uint8_t v___x_421_; 
v___x_421_ = lean_nat_dec_le(v___y_420_, v___x_418_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v___x_418_);
lean_inc(v___y_420_);
v___x_422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_415_, v_deps_414_, v___y_420_, v___y_420_);
lean_dec(v___y_420_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_415_, v_deps_414_, v___y_420_, v___x_418_);
lean_dec(v___x_418_);
return v___x_423_;
}
}
}
else
{
return v_deps_414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_425_, lean_object* v_e_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_425_, v_e_426_);
lean_dec_ref(v_e_426_);
lean_dec_ref(v_fvars_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_428_, lean_object* v_as_429_, lean_object* v_lo_430_, lean_object* v_hi_431_, lean_object* v_w_432_, lean_object* v_hlo_433_, lean_object* v_hhi_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_428_, v_as_429_, v_lo_430_, v_hi_431_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_436_, lean_object* v_as_437_, lean_object* v_lo_438_, lean_object* v_hi_439_, lean_object* v_w_440_, lean_object* v_hlo_441_, lean_object* v_hhi_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_436_, v_as_437_, v_lo_438_, v_hi_439_, v_w_440_, v_hlo_441_, v_hhi_442_);
lean_dec(v_hi_439_);
lean_dec(v_n_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object* v_n_444_, lean_object* v_lo_445_, lean_object* v_hi_446_, lean_object* v_hhi_447_, lean_object* v_pivot_448_, lean_object* v_as_449_, lean_object* v_i_450_, lean_object* v_k_451_, lean_object* v_ilo_452_, lean_object* v_ik_453_, lean_object* v_w_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_446_, v_pivot_448_, v_as_449_, v_i_450_, v_k_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object* v_n_456_, lean_object* v_lo_457_, lean_object* v_hi_458_, lean_object* v_hhi_459_, lean_object* v_pivot_460_, lean_object* v_as_461_, lean_object* v_i_462_, lean_object* v_k_463_, lean_object* v_ilo_464_, lean_object* v_ik_465_, lean_object* v_w_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_456_, v_lo_457_, v_hi_458_, v_hhi_459_, v_pivot_460_, v_as_461_, v_i_462_, v_k_463_, v_ilo_464_, v_ik_465_, v_w_466_);
lean_dec(v_pivot_460_);
lean_dec(v_hi_458_);
lean_dec(v_lo_457_);
lean_dec(v_n_456_);
return v_res_467_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_468_, size_t v_sz_469_, size_t v_i_470_, lean_object* v_bs_471_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_470_, v_sz_469_);
if (v___x_472_ == 0)
{
return v_bs_471_;
}
else
{
lean_object* v_v_473_; uint8_t v_binderInfo_474_; uint8_t v_hasFwdDeps_475_; lean_object* v_backDeps_476_; uint8_t v_isProp_477_; uint8_t v_isDecInst_478_; uint8_t v_isInstance_479_; uint8_t v_higherOrderOutParam_480_; uint8_t v_dependsOnHigherOrderOutParam_481_; lean_object* v___x_482_; lean_object* v_bs_x27_483_; lean_object* v___y_485_; 
v_v_473_ = lean_array_uget(v_bs_471_, v_i_470_);
v_binderInfo_474_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1);
v_hasFwdDeps_475_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 1);
v_backDeps_476_ = lean_ctor_get(v_v_473_, 0);
v_isProp_477_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 2);
v_isDecInst_478_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 3);
v_isInstance_479_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_480_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_481_ = lean_ctor_get_uint8(v_v_473_, sizeof(void*)*1 + 6);
v___x_482_ = lean_unsigned_to_nat(0u);
v_bs_x27_483_ = lean_array_uset(v_bs_471_, v_i_470_, v___x_482_);
if (v_hasFwdDeps_475_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_usize_to_nat(v_i_470_);
v___x_491_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_468_, v___x_490_);
lean_dec(v___x_490_);
if (v___x_491_ == 0)
{
v___y_485_ = v_v_473_;
goto v___jp_484_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_inc_ref(v_backDeps_476_);
v_isSharedCheck_498_ = !lean_is_exclusive(v_v_473_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_v_473_, 0);
lean_dec(v_unused_499_);
v___x_493_ = v_v_473_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_v_473_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_backDeps_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1, v_binderInfo_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1 + 2, v_isProp_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1 + 3, v_isDecInst_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1 + 4, v_isInstance_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1 + 5, v_higherOrderOutParam_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_481_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1 + 1, v___x_491_);
v___y_485_ = v___x_496_;
goto v___jp_484_;
}
}
}
}
else
{
v___y_485_ = v_v_473_;
goto v___jp_484_;
}
v___jp_484_:
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_470_, v___x_486_);
v___x_488_ = lean_array_uset(v_bs_x27_483_, v_i_470_, v___y_485_);
v_i_470_ = v___x_487_;
v_bs_471_ = v___x_488_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_backDeps_468_ = stack[0].m_obj;
size_t v_sz_469_ = stack[1].m_num;
size_t v_i_470_ = stack[2].m_num;
lean_object* v_bs_471_ = stack[3].m_obj;
lean_object* v_res_500_;
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_468_, v_sz_469_, v_i_470_, v_bs_471_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_501_, lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_bs_504_){
_start:
{
size_t v_sz_boxed_505_; size_t v_i_boxed_506_; lean_object* v_res_507_; 
v_sz_boxed_505_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_506_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_501_, v_sz_boxed_505_, v_i_boxed_506_, v_bs_504_);
lean_dec_ref(v_backDeps_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_508_, lean_object* v_backDeps_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_array_get_size(v_backDeps_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; 
v_sz_513_ = lean_array_size(v_pinfo_508_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_509_, v_sz_513_, v___x_514_, v_pinfo_508_);
return v___x_515_;
}
else
{
return v_pinfo_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_516_, lean_object* v_backDeps_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_516_, v_backDeps_517_);
lean_dec_ref(v_backDeps_517_);
return v_res_518_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_519_, lean_object* v_as_520_, size_t v_sz_521_, size_t v_i_522_, lean_object* v_bs_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_519_, v_sz_521_, v_i_522_, v_bs_523_);
return v___x_524_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_backDeps_519_ = stack[0].m_obj;
lean_object* v_as_520_ = stack[1].m_obj;
size_t v_sz_521_ = stack[2].m_num;
size_t v_i_522_ = stack[3].m_num;
lean_object* v_bs_523_ = stack[4].m_obj;
lean_object* v_res_525_;
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_519_, v_as_520_, v_sz_521_, v_i_522_, v_bs_523_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_526_, lean_object* v_as_527_, lean_object* v_sz_528_, lean_object* v_i_529_, lean_object* v_bs_530_){
_start:
{
size_t v_sz_boxed_531_; size_t v_i_boxed_532_; lean_object* v_res_533_; 
v_sz_boxed_531_ = lean_unbox_usize(v_sz_528_);
lean_dec(v_sz_528_);
v_i_boxed_532_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_526_, v_as_527_, v_sz_boxed_531_, v_i_boxed_532_, v_bs_530_);
lean_dec_ref(v_as_527_);
lean_dec_ref(v_backDeps_526_);
return v_res_533_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_534_, lean_object* v_b_535_, lean_object* v_c_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; 
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_542_ = lean_apply_7(v_k_534_, v_b_535_, v_c_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
return v___x_542_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_534_ = stack[0].m_obj;
lean_object* v_b_535_ = stack[1].m_obj;
lean_object* v_c_536_ = stack[2].m_obj;
lean_object* v___y_537_ = stack[3].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v___y_540_ = stack[6].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_534_, v_b_535_, v_c_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_544_, lean_object* v_b_545_, lean_object* v_c_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_544_, v_b_545_, v_c_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_553_, lean_object* v_k_554_, uint8_t v_cleanupAnnotations_555_, uint8_t v_whnfType_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___f_562_; lean_object* v___x_563_; 
v___f_562_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_562_, 0, v_k_554_);
v___x_563_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_553_, v___f_562_, v_cleanupAnnotations_555_, v_whnfType_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_563_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_563_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_553_ = stack[0].m_obj;
lean_object* v_k_554_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_555_ = stack[2].m_num;
uint8_t v_whnfType_556_ = stack[3].m_num;
lean_object* v___y_557_ = stack[4].m_obj;
lean_object* v___y_558_ = stack[5].m_obj;
lean_object* v___y_559_ = stack[6].m_obj;
lean_object* v___y_560_ = stack[7].m_obj;
lean_object* v_res_580_;
v_res_580_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_553_, v_k_554_, v_cleanupAnnotations_555_, v_whnfType_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_581_, lean_object* v_k_582_, lean_object* v_cleanupAnnotations_583_, lean_object* v_whnfType_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_590_; uint8_t v_whnfType_boxed_591_; lean_object* v_res_592_; 
v_cleanupAnnotations_boxed_590_ = lean_unbox(v_cleanupAnnotations_583_);
v_whnfType_boxed_591_ = lean_unbox(v_whnfType_584_);
v_res_592_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_581_, v_k_582_, v_cleanupAnnotations_boxed_590_, v_whnfType_boxed_591_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_592_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_593_, lean_object* v_type_594_, lean_object* v_k_595_, uint8_t v_cleanupAnnotations_596_, uint8_t v_whnfType_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_594_, v_k_595_, v_cleanupAnnotations_596_, v_whnfType_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
return v___x_603_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_594_ = stack[1].m_obj;
lean_object* v_k_595_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_596_ = stack[3].m_num;
uint8_t v_whnfType_597_ = stack[4].m_num;
lean_object* v___y_598_ = stack[5].m_obj;
lean_object* v___y_599_ = stack[6].m_obj;
lean_object* v___y_600_ = stack[7].m_obj;
lean_object* v___y_601_ = stack[8].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_box(0), v_type_594_, v_k_595_, v_cleanupAnnotations_596_, v_whnfType_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_605_, lean_object* v_type_606_, lean_object* v_k_607_, lean_object* v_cleanupAnnotations_608_, lean_object* v_whnfType_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_615_; uint8_t v_whnfType_boxed_616_; lean_object* v_res_617_; 
v_cleanupAnnotations_boxed_615_ = lean_unbox(v_cleanupAnnotations_608_);
v_whnfType_boxed_616_ = lean_unbox(v_whnfType_609_);
v_res_617_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_605_, v_type_606_, v_k_607_, v_cleanupAnnotations_boxed_615_, v_whnfType_boxed_616_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_617_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_8495__overap_626_; lean_object* v___x_627_; 
v___f_625_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_8495__overap_626_ = lean_panic_fn_borrowed(v___f_625_, v_msg_619_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
v___x_627_ = lean_apply_5(v___x_8495__overap_626_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, lean_box(0));
return v___x_627_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_619_ = stack[0].m_obj;
lean_object* v___y_620_ = stack[1].m_obj;
lean_object* v___y_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_636_, lean_object* v_maxFVars_x3f_637_, lean_object* v_k_638_, uint8_t v_cleanupAnnotations_639_, uint8_t v_whnfType_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___f_646_; lean_object* v___x_647_; 
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_646_, 0, v_k_638_);
v___x_647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_636_, v_maxFVars_x3f_637_, v___f_646_, v_cleanupAnnotations_639_, v_whnfType_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_647_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_636_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_637_ = stack[1].m_obj;
lean_object* v_k_638_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_639_ = stack[3].m_num;
uint8_t v_whnfType_640_ = stack[4].m_num;
lean_object* v___y_641_ = stack[5].m_obj;
lean_object* v___y_642_ = stack[6].m_obj;
lean_object* v___y_643_ = stack[7].m_obj;
lean_object* v___y_644_ = stack[8].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_636_, v_maxFVars_x3f_637_, v_k_638_, v_cleanupAnnotations_639_, v_whnfType_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_665_, lean_object* v_maxFVars_x3f_666_, lean_object* v_k_667_, lean_object* v_cleanupAnnotations_668_, lean_object* v_whnfType_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_675_; uint8_t v_whnfType_boxed_676_; lean_object* v_res_677_; 
v_cleanupAnnotations_boxed_675_ = lean_unbox(v_cleanupAnnotations_668_);
v_whnfType_boxed_676_ = lean_unbox(v_whnfType_669_);
v_res_677_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_665_, v_maxFVars_x3f_666_, v_k_667_, v_cleanupAnnotations_boxed_675_, v_whnfType_boxed_676_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_677_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_678_, lean_object* v_type_679_, lean_object* v_maxFVars_x3f_680_, lean_object* v_k_681_, uint8_t v_cleanupAnnotations_682_, uint8_t v_whnfType_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_679_, v_maxFVars_x3f_680_, v_k_681_, v_cleanupAnnotations_682_, v_whnfType_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_679_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_680_ = stack[2].m_obj;
lean_object* v_k_681_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_682_ = stack[4].m_num;
uint8_t v_whnfType_683_ = stack[5].m_num;
lean_object* v___y_684_ = stack[6].m_obj;
lean_object* v___y_685_ = stack[7].m_obj;
lean_object* v___y_686_ = stack[8].m_obj;
lean_object* v___y_687_ = stack[9].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_box(0), v_type_679_, v_maxFVars_x3f_680_, v_k_681_, v_cleanupAnnotations_682_, v_whnfType_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_691_, lean_object* v_type_692_, lean_object* v_maxFVars_x3f_693_, lean_object* v_k_694_, lean_object* v_cleanupAnnotations_695_, lean_object* v_whnfType_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_702_; uint8_t v_whnfType_boxed_703_; lean_object* v_res_704_; 
v_cleanupAnnotations_boxed_702_ = lean_unbox(v_cleanupAnnotations_695_);
v_whnfType_boxed_703_ = lean_unbox(v_whnfType_696_);
v_res_704_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_691_, v_type_692_, v_maxFVars_x3f_693_, v_k_694_, v_cleanupAnnotations_boxed_702_, v_whnfType_boxed_703_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_704_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_705_, lean_object* v_val_706_, lean_object* v___x_707_, lean_object* v_fvars_708_, lean_object* v_next_709_, lean_object* v_upperBound_710_, lean_object* v_a_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_a_719_; uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_lt(v_a_711_, v_upperBound_705_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v_a_711_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v_b_712_);
return v___x_724_;
}
else
{
lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_790_; 
v_fst_725_ = lean_ctor_get(v_b_712_, 0);
v_snd_726_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_790_ == 0)
{
v___x_728_ = v_b_712_;
v_isShared_729_ = v_isSharedCheck_790_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_inc(v_fst_725_);
lean_dec(v_b_712_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_790_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; 
v___x_730_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_706_, v_a_711_);
if (v___x_730_ == 0)
{
lean_object* v___x_732_; 
if (v_isShared_729_ == 0)
{
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fst_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_726_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v_a_719_ = v___x_732_;
goto v___jp_718_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_array_fget_borrowed(v___x_707_, v_a_711_);
v___x_735_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_708_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 1)
{
lean_object* v_val_736_; uint8_t v___x_737_; lean_object* v___x_738_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_nat_dec_lt(v_next_709_, v_upperBound_710_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___x_734_);
v___x_738_ = lean_infer_type(v___x_734_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
v___x_740_ = lean_whnf(v_a_739_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___y_743_; uint8_t v___x_749_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_749_ = l_Lean_Expr_isForall(v_a_741_);
lean_dec(v_a_741_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec(v_val_736_);
lean_del_object(v___x_728_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_fst_725_);
lean_ctor_set(v___x_750_, 1, v_snd_726_);
v_a_719_ = v___x_750_;
goto v___jp_718_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_fst_725_);
v___x_752_ = lean_nat_dec_lt(v_val_736_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_val_736_);
v___y_743_ = v_fst_725_;
goto v___jp_742_;
}
else
{
lean_object* v_v_753_; uint8_t v_binderInfo_754_; uint8_t v_hasFwdDeps_755_; lean_object* v_backDeps_756_; uint8_t v_isProp_757_; uint8_t v_isDecInst_758_; uint8_t v_isInstance_759_; uint8_t v_dependsOnHigherOrderOutParam_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
v_v_753_ = lean_array_fget(v_fst_725_, v_val_736_);
v_binderInfo_754_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1);
v_hasFwdDeps_755_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1 + 1);
v_backDeps_756_ = lean_ctor_get(v_v_753_, 0);
v_isProp_757_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1 + 2);
v_isDecInst_758_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1 + 3);
v_isInstance_759_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_760_ = lean_ctor_get_uint8(v_v_753_, sizeof(void*)*1 + 6);
v_isSharedCheck_770_ = !lean_is_exclusive(v_v_753_);
if (v_isSharedCheck_770_ == 0)
{
v___x_762_ = v_v_753_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_backDeps_756_);
lean_dec(v_v_753_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v_xs_x27_765_; lean_object* v___x_767_; 
v___x_764_ = lean_box(0);
v_xs_x27_765_ = lean_array_fset(v_fst_725_, v_val_736_, v___x_764_);
if (v_isShared_763_ == 0)
{
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_backDeps_756_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1, v_binderInfo_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1 + 1, v_hasFwdDeps_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1 + 2, v_isProp_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1 + 3, v_isDecInst_758_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1 + 4, v_isInstance_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_760_);
v___x_767_ = v_reuseFailAlloc_769_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; 
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*1 + 5, v___x_737_);
v___x_768_ = lean_array_fset(v_xs_x27_765_, v_val_736_, v___x_767_);
lean_dec(v_val_736_);
v___y_743_ = v___x_768_;
goto v___jp_742_;
}
}
}
}
v___jp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = l_Lean_Expr_fvarId_x21(v___x_734_);
v___x_745_ = l_Lean_FVarIdSet_insert(v_snd_726_, v___x_744_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_745_);
lean_ctor_set(v___x_728_, 0, v___y_743_);
v___x_747_ = v___x_728_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___y_743_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
v_a_719_ = v___x_747_;
goto v___jp_718_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_val_736_);
lean_del_object(v___x_728_);
lean_dec(v_snd_726_);
lean_dec(v_fst_725_);
lean_dec(v_a_711_);
v_a_771_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_740_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_740_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_val_736_);
lean_del_object(v___x_728_);
lean_dec(v_snd_726_);
lean_dec(v_fst_725_);
lean_dec(v_a_711_);
v_a_779_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_738_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_738_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v___x_735_);
if (v_isShared_729_ == 0)
{
v___x_788_ = v___x_728_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_725_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_snd_726_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
v_a_719_ = v___x_788_;
goto v___jp_718_;
}
}
}
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_a_711_, v___x_720_);
lean_dec(v_a_711_);
v_a_711_ = v___x_721_;
v_b_712_ = v_a_719_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_705_ = stack[0].m_obj;
lean_object* v_val_706_ = stack[1].m_obj;
lean_object* v___x_707_ = stack[2].m_obj;
lean_object* v_fvars_708_ = stack[3].m_obj;
lean_object* v_next_709_ = stack[4].m_obj;
lean_object* v_upperBound_710_ = stack[5].m_obj;
lean_object* v_a_711_ = stack[6].m_obj;
lean_object* v_b_712_ = stack[7].m_obj;
lean_object* v___y_713_ = stack[8].m_obj;
lean_object* v___y_714_ = stack[9].m_obj;
lean_object* v___y_715_ = stack[10].m_obj;
lean_object* v___y_716_ = stack[11].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_705_, v_val_706_, v___x_707_, v_fvars_708_, v_next_709_, v_upperBound_710_, v_a_711_, v_b_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_792_, lean_object* v_val_793_, lean_object* v___x_794_, lean_object* v_fvars_795_, lean_object* v_next_796_, lean_object* v_upperBound_797_, lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_792_, v_val_793_, v___x_794_, v_fvars_795_, v_next_796_, v_upperBound_797_, v_a_798_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v_upperBound_797_);
lean_dec(v_next_796_);
lean_dec_ref(v_fvars_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v_val_793_);
lean_dec(v_upperBound_792_);
return v_res_805_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_809_, lean_object* v_type_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_816_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_817_ = l_Lean_Expr_isAppOf(v_type_810_, v___x_816_);
v___x_818_ = lean_box(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_809_ = stack[0].m_obj;
lean_object* v_type_810_ = stack[1].m_obj;
lean_object* v___y_811_ = stack[2].m_obj;
lean_object* v___y_812_ = stack[3].m_obj;
lean_object* v___y_813_ = stack[4].m_obj;
lean_object* v___y_814_ = stack[5].m_obj;
lean_object* v_res_820_;
v_res_820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_809_, v_type_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_821_, lean_object* v_type_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_821_, v_type_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v_type_822_);
lean_dec_ref(v_x_821_);
return v_res_828_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_k_829_, lean_object* v_t_830_){
_start:
{
if (lean_obj_tag(v_t_830_) == 0)
{
lean_object* v_k_831_; lean_object* v_l_832_; lean_object* v_r_833_; uint8_t v___x_834_; 
v_k_831_ = lean_ctor_get(v_t_830_, 1);
v_l_832_ = lean_ctor_get(v_t_830_, 3);
v_r_833_ = lean_ctor_get(v_t_830_, 4);
v___x_834_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_829_, v_k_831_);
switch(v___x_834_)
{
case 0:
{
v_t_830_ = v_l_832_;
goto _start;
}
case 1:
{
uint8_t v___x_836_; 
v___x_836_ = 1;
return v___x_836_;
}
default: 
{
v_t_830_ = v_r_833_;
goto _start;
}
}
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_829_ = stack[0].m_obj;
lean_object* v_t_830_ = stack[1].m_obj;
uint8_t v_res_839_;
v_res_839_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_829_, v_t_830_);
stack->m_num = v_res_839_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_k_840_, lean_object* v_t_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_840_, v_t_841_);
lean_dec(v_t_841_);
lean_dec(v_k_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object* v_snd_844_, lean_object* v_e_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_Expr_isFVar(v_e_845_);
if (v___x_846_ == 0)
{
return v___x_846_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = l_Lean_Expr_fvarId_x21(v_e_845_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_847_, v_snd_844_);
lean_dec(v___x_847_);
return v___x_848_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_844_ = stack[0].m_obj;
lean_object* v_e_845_ = stack[1].m_obj;
uint8_t v_res_849_;
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_844_, v_e_845_);
stack->m_num = v_res_849_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object* v_snd_850_, lean_object* v_e_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_850_, v_e_851_);
lean_dec_ref(v_e_851_);
lean_dec(v_snd_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_855_; lean_object* v_dummy_856_; 
v___x_855_ = lean_box(0);
v_dummy_856_ = l_Lean_Expr_sort___override(v___x_855_);
return v_dummy_856_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_860_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_861_ = lean_unsigned_to_nat(47u);
v___x_862_ = lean_unsigned_to_nat(121u);
v___x_863_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_864_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_865_ = l_mkPanicMessageWithDecl(v___x_864_, v___x_863_, v___x_862_, v___x_861_, v___x_860_);
return v___x_865_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_866_, lean_object* v_fvars_867_, lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_a_876_; uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_lt(v_a_868_, v_upperBound_866_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_a_868_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_b_869_);
return v___x_881_;
}
else
{
lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_1003_; 
v_fst_882_ = lean_ctor_get(v_b_869_, 0);
v_snd_883_ = lean_ctor_get(v_b_869_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_869_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_885_ = v_b_869_;
v_isShared_886_ = v_isSharedCheck_1003_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_snd_883_);
lean_inc(v_fst_882_);
lean_dec(v_b_869_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_1003_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___f_887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
lean_inc(v_snd_883_);
v___f_888_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_888_, 0, v_snd_883_);
v___x_889_ = lean_array_fget_borrowed(v_fvars_867_, v_a_868_);
v___x_890_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_889_, v___y_870_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___y_977_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Lean_LocalDecl_type(v_a_891_);
v___x_893_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_867_, v___x_892_);
if (lean_obj_tag(v_snd_883_) == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_find_expr(v___f_888_, v___x_892_);
lean_dec_ref(v___f_888_);
if (lean_obj_tag(v___x_992_) == 0)
{
uint8_t v___x_993_; 
v___x_993_ = 0;
v___y_977_ = v___x_993_;
goto v___jp_976_;
}
else
{
lean_dec_ref_known(v___x_992_, 1);
v___y_977_ = v___x_880_;
goto v___jp_976_;
}
}
else
{
uint8_t v___x_994_; 
lean_dec_ref(v___f_888_);
v___x_994_ = 0;
v___y_977_ = v___x_994_;
goto v___jp_976_;
}
v___jp_894_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_882_, v___x_893_);
lean_inc_ref(v___x_892_);
v___x_899_ = l_Lean_Meta_isProp(v___x_892_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; uint8_t v___x_901_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = 0;
lean_inc_ref(v___x_892_);
v___x_902_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_892_, v___f_887_, v___x_901_, v___x_901_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; uint8_t v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = l_Lean_LocalDecl_binderInfo(v_a_891_);
lean_dec(v_a_891_);
v___x_905_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_905_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_904_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 1, v___x_901_);
v___x_906_ = lean_unbox(v_a_900_);
lean_dec(v_a_900_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 2, v___x_906_);
v___x_907_ = lean_unbox(v_a_903_);
lean_dec(v_a_903_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 3, v___x_907_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 4, v___y_897_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 5, v___x_901_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1 + 6, v___y_895_);
v___x_908_ = lean_array_push(v___x_898_, v___x_905_);
if (v___y_897_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v___y_896_);
lean_dec_ref(v___x_892_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_908_);
v___x_910_ = v___x_885_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_snd_883_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v_a_876_ = v___x_910_;
goto v___jp_875_;
}
}
else
{
if (lean_obj_tag(v___y_896_) == 1)
{
lean_object* v_val_912_; lean_object* v___x_913_; lean_object* v_env_914_; lean_object* v___x_915_; 
v_val_912_ = lean_ctor_get(v___y_896_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v___y_896_, 1);
v___x_913_ = lean_st_ref_get(v___y_873_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_914_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_getOutParamPositions_x3f(v_env_914_, v_val_912_);
lean_dec(v_val_912_);
if (lean_obj_tag(v___x_915_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_val_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_array_get_size(v_val_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v_dummy_920_; lean_object* v_nargs_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_dummy_920_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_921_ = l_Lean_Expr_getAppNumArgs(v___x_892_);
lean_inc(v_nargs_921_);
v___x_922_ = lean_mk_array(v_nargs_921_, v_dummy_920_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_sub(v_nargs_921_, v___x_923_);
lean_dec(v_nargs_921_);
v___x_925_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_892_, v___x_922_, v___x_924_);
v___x_926_ = lean_array_get_size(v___x_925_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_908_);
v___x_928_ = v___x_885_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_snd_883_);
v___x_928_ = v_reuseFailAlloc_940_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_926_, v_val_916_, v___x_925_, v_fvars_867_, v_a_868_, v_upperBound_866_, v___x_918_, v___x_928_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec_ref(v___x_925_);
lean_dec(v_val_916_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v_fst_931_ = lean_ctor_get(v_a_930_, 0);
v_snd_932_ = lean_ctor_get(v_a_930_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v_a_930_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_snd_932_);
lean_inc(v_fst_931_);
lean_dec(v_a_930_);
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
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
v_a_876_ = v___x_937_;
goto v___jp_875_;
}
}
}
else
{
lean_dec(v_a_868_);
return v___x_929_;
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec(v_val_916_);
lean_dec_ref(v___x_892_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_908_);
v___x_942_ = v___x_885_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_snd_883_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
v_a_876_ = v___x_942_;
goto v___jp_875_;
}
}
}
else
{
lean_object* v___x_945_; 
lean_dec(v___x_915_);
lean_dec_ref(v___x_892_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_908_);
v___x_945_ = v___x_885_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_snd_883_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_a_876_ = v___x_945_;
goto v___jp_875_;
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v___y_896_);
lean_dec_ref(v___x_892_);
v___x_947_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
v___x_948_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_947_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_950_; 
lean_dec_ref_known(v___x_948_, 1);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_908_);
v___x_950_ = v___x_885_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_snd_883_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v_a_876_ = v___x_950_;
goto v___jp_875_;
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v___x_908_);
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_a_868_);
v_a_952_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_948_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_a_900_);
lean_dec_ref(v___x_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
lean_dec(v_a_891_);
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_a_868_);
v_a_960_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_902_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_902_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___x_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
lean_dec(v_a_891_);
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_a_868_);
v_a_968_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_899_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_899_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
v___jp_976_:
{
lean_object* v___x_978_; 
lean_inc_ref(v___x_892_);
v___x_978_ = l_Lean_Meta_isClass_x3f(v___x_892_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
if (lean_obj_tag(v_a_979_) == 0)
{
uint8_t v___x_980_; 
v___x_980_ = 0;
v___y_895_ = v___y_977_;
v___y_896_ = v_a_979_;
v___y_897_ = v___x_980_;
goto v___jp_894_;
}
else
{
uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_LocalDecl_binderInfo(v_a_891_);
v___x_982_ = l_Lean_BinderInfo_isExplicit(v___x_981_);
if (v___x_982_ == 0)
{
v___y_895_ = v___y_977_;
v___y_896_ = v_a_979_;
v___y_897_ = v___x_880_;
goto v___jp_894_;
}
else
{
uint8_t v___x_983_; 
v___x_983_ = 0;
v___y_895_ = v___y_977_;
v___y_896_ = v_a_979_;
v___y_897_ = v___x_983_;
goto v___jp_894_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
lean_dec(v_a_891_);
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec(v_a_868_);
v_a_984_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_978_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___f_888_);
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec(v_a_868_);
v_a_995_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_890_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_890_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
v___jp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_a_868_, v___x_877_);
lean_dec(v_a_868_);
v_a_868_ = v___x_878_;
v_b_869_ = v_a_876_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_866_ = stack[0].m_obj;
lean_object* v_fvars_867_ = stack[1].m_obj;
lean_object* v_a_868_ = stack[2].m_obj;
lean_object* v_b_869_ = stack[3].m_obj;
lean_object* v___y_870_ = stack[4].m_obj;
lean_object* v___y_871_ = stack[5].m_obj;
lean_object* v___y_872_ = stack[6].m_obj;
lean_object* v___y_873_ = stack[7].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_866_, v_fvars_867_, v_a_868_, v_b_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_1005_, lean_object* v_fvars_1006_, lean_object* v_a_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_1005_, v_fvars_1006_, v_a_1007_, v_b_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_fvars_1006_);
lean_dec(v_upperBound_1005_);
return v_res_1014_;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_1017_, lean_object* v_fvars_1018_, lean_object* v_type_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1025_ = lean_array_get_size(v_fvars_1018_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1017_);
v___x_1029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1025_, v_fvars_1018_, v___x_1026_, v___x_1028_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1048_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1048_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1048_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1046_; 
v_fst_1034_ = lean_ctor_get(v_a_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_a_1030_, 1);
lean_dec(v_unused_1047_);
v___x_1036_ = v_a_1030_;
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_fst_1034_);
lean_dec(v_a_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_1018_, v_type_1019_);
v___x_1039_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_1034_, v___x_1038_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1038_);
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1038_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1041_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_a_1049_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1029_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1029_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1017_ = stack[0].m_obj;
lean_object* v_fvars_1018_ = stack[1].m_obj;
lean_object* v_type_1019_ = stack[2].m_obj;
lean_object* v___y_1020_ = stack[3].m_obj;
lean_object* v___y_1021_ = stack[4].m_obj;
lean_object* v___y_1022_ = stack[5].m_obj;
lean_object* v___y_1023_ = stack[6].m_obj;
lean_object* v_res_1057_;
v_res_1057_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1017_, v_fvars_1018_, v_type_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1057_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_1058_, lean_object* v_fvars_1059_, lean_object* v_type_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1058_, v_fvars_1059_, v_type_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec_ref(v_type_1060_);
lean_dec_ref(v_fvars_1059_);
return v_res_1066_;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1067_, lean_object* v_maxArgs_x3f_1068_, lean_object* v___f_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___y_1076_; lean_object* v___x_1093_; 
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
v___x_1093_ = lean_infer_type(v_fn_1067_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; uint8_t v_transparency_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l_Lean_Meta_Context_config(v___y_1070_);
v_transparency_1096_ = lean_ctor_get_uint8(v___x_1095_, 9);
lean_dec_ref(v___x_1095_);
v___x_1097_ = 1;
v___x_1098_ = 0;
v___x_1099_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1096_, v___x_1097_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1094_, v_maxArgs_x3f_1068_, v___f_1069_, v___x_1098_, v___x_1098_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
v___y_1076_ = v___x_1100_;
goto v___jp_1075_;
}
else
{
lean_object* v_keyedConfig_1101_; uint8_t v_trackZetaDelta_1102_; lean_object* v_zetaDeltaSet_1103_; lean_object* v_lctx_1104_; lean_object* v_localInstances_1105_; lean_object* v_defEqCtx_x3f_1106_; lean_object* v_synthPendingDepth_1107_; lean_object* v_customCanUnfoldPredicate_x3f_1108_; uint8_t v_univApprox_1109_; uint8_t v_inTypeClassResolution_1110_; uint8_t v_cacheInferType_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_keyedConfig_1101_ = lean_ctor_get(v___y_1070_, 0);
v_trackZetaDelta_1102_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*7);
v_zetaDeltaSet_1103_ = lean_ctor_get(v___y_1070_, 1);
v_lctx_1104_ = lean_ctor_get(v___y_1070_, 2);
v_localInstances_1105_ = lean_ctor_get(v___y_1070_, 3);
v_defEqCtx_x3f_1106_ = lean_ctor_get(v___y_1070_, 4);
v_synthPendingDepth_1107_ = lean_ctor_get(v___y_1070_, 5);
v_customCanUnfoldPredicate_x3f_1108_ = lean_ctor_get(v___y_1070_, 6);
v_univApprox_1109_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1110_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*7 + 2);
v_cacheInferType_1111_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*7 + 3);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___y_1070_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v___y_1070_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1108_);
lean_inc(v_synthPendingDepth_1107_);
lean_inc(v_defEqCtx_x3f_1106_);
lean_inc(v_localInstances_1105_);
lean_inc(v_lctx_1104_);
lean_inc(v_zetaDeltaSet_1103_);
lean_inc(v_keyedConfig_1101_);
lean_dec(v___y_1070_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1097_, v_keyedConfig_1101_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_zetaDeltaSet_1103_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_lctx_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_localInstances_1105_);
lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_defEqCtx_x3f_1106_);
lean_ctor_set(v_reuseFailAlloc_1119_, 5, v_synthPendingDepth_1107_);
lean_ctor_set(v_reuseFailAlloc_1119_, 6, v_customCanUnfoldPredicate_x3f_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*7, v_trackZetaDelta_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*7 + 1, v_univApprox_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*7 + 3, v_cacheInferType_1111_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1094_, v_maxArgs_x3f_1068_, v___f_1069_, v___x_1098_, v___x_1098_, v___x_1117_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___x_1117_);
v___y_1076_ = v___x_1118_;
goto v___jp_1075_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v___f_1069_);
lean_dec(v_maxArgs_x3f_1068_);
v_a_1121_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1093_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1093_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
v___jp_1075_:
{
if (lean_obj_tag(v___y_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___y_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___y_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___y_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___y_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___y_1076_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___y_1076_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___y_1076_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___y_1076_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1067_ = stack[0].m_obj;
lean_object* v_maxArgs_x3f_1068_ = stack[1].m_obj;
lean_object* v___f_1069_ = stack[2].m_obj;
lean_object* v___y_1070_ = stack[3].m_obj;
lean_object* v___y_1071_ = stack[4].m_obj;
lean_object* v___y_1072_ = stack[5].m_obj;
lean_object* v___y_1073_ = stack[6].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1067_, v_maxArgs_x3f_1068_, v___f_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
stack->m_obj
 = v_res_1129_;
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
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1158_, size_t v_x_1159_, lean_object* v_x_1160_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1158_ = stack[0].m_obj;
size_t v_x_1159_ = stack[1].m_num;
lean_object* v_x_1160_ = stack[2].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1158_, v_x_1159_, v_x_1160_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
size_t v_x_12087__boxed_1185_; lean_object* v_res_1186_; 
v_x_12087__boxed_1185_ = lean_unbox_usize(v_x_1183_);
lean_dec(v_x_1183_);
v_res_1186_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1182_, v_x_12087__boxed_1185_, v_x_1184_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_x_1182_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
uint64_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1188_);
v___x_1190_ = lean_uint64_to_usize(v___x_1189_);
v___x_1191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1187_, v___x_1190_, v_x_1188_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1192_, v_x_1193_);
lean_dec_ref(v_x_1193_);
lean_dec_ref(v_x_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_ks_1199_; lean_object* v_vs_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1224_; 
v_ks_1199_ = lean_ctor_get(v_x_1195_, 0);
v_vs_1200_ = lean_ctor_get(v_x_1195_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1195_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1202_ = v_x_1195_;
v_isShared_1203_ = v_isSharedCheck_1224_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_vs_1200_);
lean_inc(v_ks_1199_);
lean_dec(v_x_1195_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1224_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_array_get_size(v_ks_1199_);
v___x_1205_ = lean_nat_dec_lt(v_x_1196_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec(v_x_1196_);
v___x_1206_ = lean_array_push(v_ks_1199_, v_x_1197_);
v___x_1207_ = lean_array_push(v_vs_1200_, v_x_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1207_);
lean_ctor_set(v___x_1202_, 0, v___x_1206_);
v___x_1209_ = v___x_1202_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
lean_object* v_k_x27_1211_; uint8_t v___x_1212_; 
v_k_x27_1211_ = lean_array_fget_borrowed(v_ks_1199_, v_x_1196_);
v___x_1212_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1197_, v_k_x27_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1214_; 
if (v_isShared_1203_ == 0)
{
v___x_1214_ = v___x_1202_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_ks_1199_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_vs_1200_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_x_1196_, v___x_1215_);
lean_dec(v_x_1196_);
v_x_1195_ = v___x_1214_;
v_x_1196_ = v___x_1216_;
goto _start;
}
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1219_ = lean_array_fset(v_ks_1199_, v_x_1196_, v_x_1197_);
v___x_1220_ = lean_array_fset(v_vs_1200_, v_x_1196_, v_x_1198_);
lean_dec(v_x_1196_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1220_);
lean_ctor_set(v___x_1202_, 0, v___x_1219_);
v___x_1222_ = v___x_1202_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1225_, lean_object* v_k_1226_, lean_object* v_v_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(v_n_1225_, v___x_1228_, v_k_1226_, v_v_1227_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1230_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1231_, size_t v_x_1232_, size_t v_x_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_object* v_es_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v_j_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_es_1236_ = lean_ctor_get(v_x_1231_, 0);
v___x_1237_ = ((size_t)31ULL);
v___x_1238_ = lean_usize_land(v_x_1232_, v___x_1237_);
v_j_1239_ = lean_usize_to_nat(v___x_1238_);
v___x_1240_ = lean_array_get_size(v_es_1236_);
v___x_1241_ = lean_nat_dec_lt(v_j_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v_j_1239_);
lean_dec(v_x_1235_);
lean_dec_ref(v_x_1234_);
return v_x_1231_;
}
else
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1280_; 
lean_inc_ref(v_es_1236_);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1231_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v_x_1231_, 0);
lean_dec(v_unused_1281_);
v___x_1243_ = v_x_1231_;
v_isShared_1244_ = v_isSharedCheck_1280_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_x_1231_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1280_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_v_1245_; lean_object* v___x_1246_; lean_object* v_xs_x27_1247_; lean_object* v___y_1249_; 
v_v_1245_ = lean_array_fget(v_es_1236_, v_j_1239_);
v___x_1246_ = lean_box(0);
v_xs_x27_1247_ = lean_array_fset(v_es_1236_, v_j_1239_, v___x_1246_);
switch(lean_obj_tag(v_v_1245_))
{
case 0:
{
lean_object* v_key_1254_; lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v_key_1254_ = lean_ctor_get(v_v_1245_, 0);
v_val_1255_ = lean_ctor_get(v_v_1245_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_v_1245_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v_v_1245_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_inc(v_key_1254_);
lean_dec(v_v_1245_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
uint8_t v___x_1259_; 
v___x_1259_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1234_, v_key_1254_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1257_);
v___x_1260_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1254_, v_val_1255_, v_x_1234_, v_x_1235_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
v___y_1249_ = v___x_1261_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_val_1255_);
lean_dec(v_key_1254_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_x_1235_);
lean_ctor_set(v___x_1257_, 0, v_x_1234_);
v___x_1263_ = v___x_1257_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_x_1234_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_x_1235_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1249_ = v___x_1263_;
goto v___jp_1248_;
}
}
}
}
case 1:
{
lean_object* v_node_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
v_node_1266_ = lean_ctor_get(v_v_1245_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_v_1245_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1268_ = v_v_1245_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_node_1266_);
lean_dec(v_v_1245_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1270_ = ((size_t)5ULL);
v___x_1271_ = lean_usize_shift_right(v_x_1232_, v___x_1270_);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_x_1233_, v___x_1272_);
v___x_1274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1266_, v___x_1271_, v___x_1273_, v_x_1234_, v_x_1235_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v___y_1249_ = v___x_1276_;
goto v___jp_1248_;
}
}
}
default: 
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_x_1234_);
lean_ctor_set(v___x_1279_, 1, v_x_1235_);
v___y_1249_ = v___x_1279_;
goto v___jp_1248_;
}
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_array_fset(v_xs_x27_1247_, v_j_1239_, v___y_1249_);
lean_dec(v_j_1239_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1250_);
v___x_1252_ = v___x_1243_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
else
{
lean_object* v_ks_1282_; lean_object* v_vs_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1301_; 
v_ks_1282_ = lean_ctor_get(v_x_1231_, 0);
v_vs_1283_ = lean_ctor_get(v_x_1231_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_x_1231_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1285_ = v_x_1231_;
v_isShared_1286_ = v_isSharedCheck_1301_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_vs_1283_);
lean_inc(v_ks_1282_);
lean_dec(v_x_1231_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1301_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_ks_1282_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_vs_1283_);
v___x_1288_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v_newNode_1289_; size_t v___x_1290_; uint8_t v___x_1291_; 
v_newNode_1289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1288_, v_x_1234_, v_x_1235_);
v___x_1290_ = ((size_t)7ULL);
v___x_1291_ = lean_usize_dec_le(v___x_1290_, v_x_1233_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1289_);
v___x_1293_ = lean_unsigned_to_nat(4u);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
lean_dec(v___x_1292_);
if (v___x_1294_ == 0)
{
lean_object* v_ks_1295_; lean_object* v_vs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_ks_1295_ = lean_ctor_get(v_newNode_1289_, 0);
lean_inc_ref(v_ks_1295_);
v_vs_1296_ = lean_ctor_get(v_newNode_1289_, 1);
lean_inc_ref(v_vs_1296_);
lean_dec_ref(v_newNode_1289_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1299_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1233_, v_ks_1295_, v_vs_1296_, v___x_1297_, v___x_1298_);
lean_dec_ref(v_vs_1296_);
lean_dec_ref(v_ks_1295_);
return v___x_1299_;
}
else
{
return v_newNode_1289_;
}
}
else
{
return v_newNode_1289_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1231_ = stack[0].m_obj;
size_t v_x_1232_ = stack[1].m_num;
size_t v_x_1233_ = stack[2].m_num;
lean_object* v_x_1234_ = stack[3].m_obj;
lean_object* v_x_1235_ = stack[4].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1231_, v_x_1232_, v_x_1233_, v_x_1234_, v_x_1235_);
stack->m_obj
 = v_res_1302_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1303_, lean_object* v_keys_1304_, lean_object* v_vals_1305_, lean_object* v_i_1306_, lean_object* v_entries_1307_){
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
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1303_ = stack[0].m_num;
lean_object* v_keys_1304_ = stack[1].m_obj;
lean_object* v_vals_1305_ = stack[2].m_obj;
lean_object* v_i_1306_ = stack[3].m_obj;
lean_object* v_entries_1307_ = stack[4].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_1303_, v_keys_1304_, v_vals_1305_, v_i_1306_, v_entries_1307_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1324_, lean_object* v_keys_1325_, lean_object* v_vals_1326_, lean_object* v_i_1327_, lean_object* v_entries_1328_){
_start:
{
size_t v_depth_boxed_1329_; lean_object* v_res_1330_; 
v_depth_boxed_1329_ = lean_unbox_usize(v_depth_1324_);
lean_dec(v_depth_1324_);
v_res_1330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1329_, v_keys_1325_, v_vals_1326_, v_i_1327_, v_entries_1328_);
lean_dec_ref(v_vals_1326_);
lean_dec_ref(v_keys_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
size_t v_x_12285__boxed_1336_; size_t v_x_12286__boxed_1337_; lean_object* v_res_1338_; 
v_x_12285__boxed_1336_ = lean_unbox_usize(v_x_1332_);
lean_dec(v_x_1332_);
v_x_12286__boxed_1337_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_res_1338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1331_, v_x_12285__boxed_1336_, v_x_12286__boxed_1337_, v_x_1334_, v_x_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
uint64_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1340_);
v___x_1343_ = lean_uint64_to_usize(v___x_1342_);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1339_, v___x_1343_, v___x_1344_, v_x_1340_, v_x_1341_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1349_, lean_object* v_env_1350_, lean_object* v_env_1351_, lean_object* v_forConst_1352_, lean_object* v_ctx_1353_, lean_object* v_realize_1354_, lean_object* v_opts_1355_, lean_object* v_key_1356_, lean_object* v_inst_1357_, lean_object* v_____r_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___y_1414_; lean_object* v___x_1419_; 
v___x_1360_ = lean_io_promise_new();
v___x_1361_ = lean_st_ref_take(v_realizeMapRef_1349_);
v___x_1419_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1361_, v_inst_1357_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1414_ = v___x_1420_;
goto v___jp_1413_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v___x_1419_, 1);
v___y_1414_ = v_val_1421_;
goto v___jp_1413_;
}
v___jp_1362_:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_st_ref_put(v_realizeMapRef_1349_, v_snd_1364_);
if (lean_obj_tag(v_fst_1363_) == 1)
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1360_);
lean_dec_ref(v_opts_1355_);
lean_dec_ref(v_realize_1354_);
lean_dec_ref(v_ctx_1353_);
lean_dec(v_forConst_1352_);
lean_dec_ref(v_env_1351_);
lean_dec(v_env_1350_);
v_val_1366_ = lean_ctor_get(v_fst_1363_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_fst_1363_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1368_ = v_fst_1363_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v_fst_1363_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_task_get_own(v_val_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v_base_1375_; lean_object* v_serverBaseExts_1376_; lean_object* v_checked_1377_; lean_object* v_asyncConstsMap_1378_; lean_object* v_asyncCtx_x3f_1379_; lean_object* v_localRealizationCtxMap_1380_; lean_object* v_allRealizations_1381_; uint8_t v_isExporting_1382_; uint8_t v_isRecordingDeps_1383_; lean_object* v_synthCacheRaw_x3f_1384_; lean_object* v_declChangeLog_1385_; lean_object* v_recordingConstGen_1386_; lean_object* v_constAddedGens_1387_; lean_object* v_constGen_1388_; lean_object* v_importRealizationCtx_x3f_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_fst_1363_);
v_base_1375_ = lean_ctor_get(v_env_1350_, 0);
lean_inc_ref(v_base_1375_);
v_serverBaseExts_1376_ = lean_ctor_get(v_env_1350_, 1);
lean_inc_ref(v_serverBaseExts_1376_);
v_checked_1377_ = lean_ctor_get(v_env_1350_, 2);
lean_inc_ref(v_checked_1377_);
v_asyncConstsMap_1378_ = lean_ctor_get(v_env_1350_, 3);
lean_inc_ref(v_asyncConstsMap_1378_);
v_asyncCtx_x3f_1379_ = lean_ctor_get(v_env_1350_, 4);
lean_inc(v_asyncCtx_x3f_1379_);
v_localRealizationCtxMap_1380_ = lean_ctor_get(v_env_1350_, 6);
lean_inc(v_localRealizationCtxMap_1380_);
v_allRealizations_1381_ = lean_ctor_get(v_env_1350_, 7);
lean_inc_ref(v_allRealizations_1381_);
v_isExporting_1382_ = lean_ctor_get_uint8(v_env_1350_, sizeof(void*)*13);
v_isRecordingDeps_1383_ = lean_ctor_get_uint8(v_env_1350_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_1384_ = lean_ctor_get(v_env_1350_, 8);
lean_inc(v_synthCacheRaw_x3f_1384_);
v_declChangeLog_1385_ = lean_ctor_get(v_env_1350_, 9);
lean_inc_ref(v_declChangeLog_1385_);
v_recordingConstGen_1386_ = lean_ctor_get(v_env_1350_, 10);
lean_inc(v_recordingConstGen_1386_);
v_constAddedGens_1387_ = lean_ctor_get(v_env_1350_, 11);
lean_inc_ref(v_constAddedGens_1387_);
v_constGen_1388_ = lean_ctor_get(v_env_1350_, 12);
lean_inc(v_constGen_1388_);
lean_dec(v_env_1350_);
v_importRealizationCtx_x3f_1389_ = lean_ctor_get(v_env_1351_, 5);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_env_1351_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1401_ = lean_ctor_get(v_env_1351_, 12);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_env_1351_, 11);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_env_1351_, 10);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_env_1351_, 9);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_env_1351_, 8);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_env_1351_, 7);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_env_1351_, 6);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_env_1351_, 4);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_env_1351_, 3);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_env_1351_, 2);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_env_1351_, 1);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_env_1351_, 0);
lean_dec(v_unused_1412_);
v___x_1391_ = v_env_1351_;
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_importRealizationCtx_x3f_1389_);
lean_dec(v_env_1351_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1352_, v_ctx_1353_, v_localRealizationCtxMap_1380_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 12, v_constGen_1388_);
lean_ctor_set(v___x_1391_, 11, v_constAddedGens_1387_);
lean_ctor_set(v___x_1391_, 10, v_recordingConstGen_1386_);
lean_ctor_set(v___x_1391_, 9, v_declChangeLog_1385_);
lean_ctor_set(v___x_1391_, 8, v_synthCacheRaw_x3f_1384_);
lean_ctor_set(v___x_1391_, 7, v_allRealizations_1381_);
lean_ctor_set(v___x_1391_, 6, v___x_1393_);
lean_ctor_set(v___x_1391_, 4, v_asyncCtx_x3f_1379_);
lean_ctor_set(v___x_1391_, 3, v_asyncConstsMap_1378_);
lean_ctor_set(v___x_1391_, 2, v_checked_1377_);
lean_ctor_set(v___x_1391_, 1, v_serverBaseExts_1376_);
lean_ctor_set(v___x_1391_, 0, v_base_1375_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_base_1375_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_serverBaseExts_1376_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_checked_1377_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_asyncConstsMap_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_asyncCtx_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_importRealizationCtx_x3f_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_allRealizations_1381_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_synthCacheRaw_x3f_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 9, v_declChangeLog_1385_);
lean_ctor_set(v_reuseFailAlloc_1399_, 10, v_recordingConstGen_1386_);
lean_ctor_set(v_reuseFailAlloc_1399_, 11, v_constAddedGens_1387_);
lean_ctor_set(v_reuseFailAlloc_1399_, 12, v_constGen_1388_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*13, v_isExporting_1382_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*13 + 1, v_isRecordingDeps_1383_);
v___x_1396_ = lean_apply_3(v_realize_1354_, v___x_1395_, v_opts_1355_, lean_box(0));
lean_inc(v___x_1396_);
v___x_1397_ = lean_io_promise_resolve(v___x_1396_, v___x_1360_);
lean_dec(v___x_1360_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
return v___x_1398_;
}
}
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1414_, v_key_1356_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = l_IO_Promise_result_x21___redArg(v___x_1360_);
v___x_1417_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1414_, v_key_1356_, v___x_1416_);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1357_, v___x_1417_, v___x_1361_);
v_fst_1363_ = v___x_1415_;
v_snd_1364_ = v___x_1418_;
goto v___jp_1362_;
}
else
{
lean_dec_ref(v___y_1414_);
lean_dec(v_inst_1357_);
lean_dec_ref(v_key_1356_);
v_fst_1363_ = v___x_1415_;
v_snd_1364_ = v___x_1361_;
goto v___jp_1362_;
}
}
}
}
LEAN_EXPORT void l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_realizeMapRef_1349_ = stack[0].m_obj;
lean_object* v_env_1350_ = stack[1].m_obj;
lean_object* v_env_1351_ = stack[2].m_obj;
lean_object* v_forConst_1352_ = stack[3].m_obj;
lean_object* v_ctx_1353_ = stack[4].m_obj;
lean_object* v_realize_1354_ = stack[5].m_obj;
lean_object* v_opts_1355_ = stack[6].m_obj;
lean_object* v_key_1356_ = stack[7].m_obj;
lean_object* v_inst_1357_ = stack[8].m_obj;
lean_object* v_____r_1358_ = stack[9].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1349_, v_env_1350_, v_env_1351_, v_forConst_1352_, v_ctx_1353_, v_realize_1354_, v_opts_1355_, v_key_1356_, v_inst_1357_, v_____r_1358_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1423_, lean_object* v_env_1424_, lean_object* v_env_1425_, lean_object* v_forConst_1426_, lean_object* v_ctx_1427_, lean_object* v_realize_1428_, lean_object* v_opts_1429_, lean_object* v_key_1430_, lean_object* v_inst_1431_, lean_object* v_____r_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1423_, v_env_1424_, v_env_1425_, v_forConst_1426_, v_ctx_1427_, v_realize_1428_, v_opts_1429_, v_key_1430_, v_inst_1431_, v_____r_1432_);
lean_dec(v_realizeMapRef_1423_);
return v_res_1434_;
}
}
lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1441_, lean_object* v_env_1442_, lean_object* v_forConst_1443_, lean_object* v_key_1444_, lean_object* v_realize_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_a_1449_; lean_object* v___y_1453_; lean_object* v_ctx_1456_; uint8_t v___x_1470_; 
v___x_1447_ = lean_io_get_num_heartbeats();
v___x_1470_ = l_Lean_Environment_isImportedConst(v_env_1442_, v_forConst_1443_);
if (v___x_1470_ == 0)
{
lean_object* v_localRealizationCtxMap_1471_; lean_object* v___x_1472_; 
v_localRealizationCtxMap_1471_ = lean_ctor_get(v_env_1442_, 6);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1471_, v_forConst_1443_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v___x_1447_);
lean_dec_ref(v_realize_1445_);
lean_dec_ref(v_key_1444_);
lean_dec_ref(v_env_1442_);
v___x_1473_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1474_ = 1;
v___x_1475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1441_, v___x_1474_);
v___x_1476_ = lean_string_append(v___x_1473_, v___x_1475_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
v___x_1479_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1443_, v___x_1474_);
v___x_1480_ = lean_string_append(v___x_1478_, v___x_1479_);
lean_dec_ref(v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
else
{
lean_object* v_val_1485_; 
v_val_1485_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v___x_1472_, 1);
v_ctx_1456_ = v_val_1485_;
goto v___jp_1455_;
}
}
else
{
lean_object* v_importRealizationCtx_x3f_1486_; 
v_importRealizationCtx_x3f_1486_ = lean_ctor_get(v_env_1442_, 5);
if (lean_obj_tag(v_importRealizationCtx_x3f_1486_) == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v___x_1447_);
lean_dec_ref(v_realize_1445_);
lean_dec_ref(v_key_1444_);
lean_dec(v_forConst_1443_);
lean_dec_ref(v_env_1442_);
lean_dec(v_inst_1441_);
v___x_1487_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
else
{
lean_object* v_val_1489_; 
v_val_1489_ = lean_ctor_get(v_importRealizationCtx_x3f_1486_, 0);
lean_inc(v_val_1489_);
v_ctx_1456_ = v_val_1489_;
goto v___jp_1455_;
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_io_set_heartbeats(v___x_1447_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1449_);
return v___x_1451_;
}
v___jp_1452_:
{
lean_object* v_a_1454_; 
v_a_1454_ = lean_ctor_get(v___y_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___y_1453_);
v_a_1449_ = v_a_1454_;
goto v___jp_1448_;
}
v___jp_1455_:
{
lean_object* v_env_1457_; lean_object* v_opts_1458_; lean_object* v_realizeMapRef_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_env_1457_ = lean_ctor_get(v_ctx_1456_, 0);
lean_inc(v_env_1457_);
v_opts_1458_ = lean_ctor_get(v_ctx_1456_, 1);
lean_inc_ref(v_opts_1458_);
v_realizeMapRef_1459_ = lean_ctor_get(v_ctx_1456_, 2);
lean_inc(v_realizeMapRef_1459_);
v___x_1460_ = lean_st_ref_get(v_realizeMapRef_1459_);
v___x_1461_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1460_, v_inst_1441_);
lean_dec(v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 1)
{
lean_object* v_val_1462_; lean_object* v___x_1463_; 
v_val_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1462_, v_key_1444_);
lean_dec(v_val_1462_);
if (lean_obj_tag(v___x_1463_) == 1)
{
lean_object* v_val_1464_; lean_object* v___x_1465_; 
lean_dec(v_realizeMapRef_1459_);
lean_dec_ref(v_opts_1458_);
lean_dec(v_env_1457_);
lean_dec_ref(v_ctx_1456_);
lean_dec_ref(v_realize_1445_);
lean_dec_ref(v_key_1444_);
lean_dec(v_forConst_1443_);
lean_dec_ref(v_env_1442_);
lean_dec(v_inst_1441_);
v_val_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = lean_task_get_own(v_val_1464_);
v_a_1449_ = v___x_1465_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v___x_1467_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1459_, v_env_1457_, v_env_1442_, v_forConst_1443_, v_ctx_1456_, v_realize_1445_, v_opts_1458_, v_key_1444_, v_inst_1441_, v___x_1466_);
lean_dec(v_realizeMapRef_1459_);
v___y_1453_ = v___x_1467_;
goto v___jp_1452_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1461_);
v___x_1468_ = lean_box(0);
v___x_1469_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1459_, v_env_1457_, v_env_1442_, v_forConst_1443_, v_ctx_1456_, v_realize_1445_, v_opts_1458_, v_key_1444_, v_inst_1441_, v___x_1468_);
lean_dec(v_realizeMapRef_1459_);
v___y_1453_ = v___x_1469_;
goto v___jp_1452_;
}
}
}
}
LEAN_EXPORT void l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1441_ = stack[0].m_obj;
lean_object* v_env_1442_ = stack[1].m_obj;
lean_object* v_forConst_1443_ = stack[2].m_obj;
lean_object* v_key_1444_ = stack[3].m_obj;
lean_object* v_realize_1445_ = stack[4].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1441_, v_env_1442_, v_forConst_1443_, v_key_1444_, v_realize_1445_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1491_, lean_object* v_env_1492_, lean_object* v_forConst_1493_, lean_object* v_key_1494_, lean_object* v_realize_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1491_, v_env_1492_, v_forConst_1493_, v_key_1494_, v_realize_1495_);
return v_res_1497_;
}
}
lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___f_1504_; lean_object* v___x_9947__overap_1505_; lean_object* v___x_1506_; 
v___f_1504_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9947__overap_1505_ = lean_panic_fn_borrowed(v___f_1504_, v_msg_1498_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
v___x_1506_ = lean_apply_5(v___x_9947__overap_1505_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, lean_box(0));
return v___x_1506_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1498_ = stack[0].m_obj;
lean_object* v___y_1499_ = stack[1].m_obj;
lean_object* v___y_1500_ = stack[2].m_obj;
lean_object* v___y_1501_ = stack[3].m_obj;
lean_object* v___y_1502_ = stack[4].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1515_, lean_object* v_inst_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
v___x_1522_ = lean_apply_5(v_realize_1515_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, lean_box(0));
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_inst_1516_);
lean_ctor_set(v___x_1527_, 1, v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_inst_1516_);
v_a_1532_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1522_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1522_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_realize_1515_ = stack[0].m_obj;
lean_object* v_inst_1516_ = stack[1].m_obj;
lean_object* v___y_1517_ = stack[2].m_obj;
lean_object* v___y_1518_ = stack[3].m_obj;
lean_object* v___y_1519_ = stack[4].m_obj;
lean_object* v___y_1520_ = stack[5].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1515_, v_inst_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1541_, lean_object* v_inst_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1541_, v_inst_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = l_Lean_Options_empty;
v___x_1550_ = l_Lean_Core_getMaxHeartbeats(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_unsigned_to_nat(16u);
v___x_1553_ = lean_mk_array(v___x_1552_, v___x_1551_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
return v___x_1556_;
}
}
static uint16_t _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1557_; uint16_t v___x_1558_; 
v___x_1557_ = l_Lean_Options_empty;
v___x_1558_ = l_Lean_OptionFlags_ofOptions(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1562_ = lean_unsigned_to_nat(36u);
v___x_1563_ = lean_unsigned_to_nat(2845u);
v___x_1564_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5));
v___x_1565_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1566_ = l_mkPanicMessageWithDecl(v___x_1565_, v___x_1564_, v___x_1563_, v___x_1562_, v___x_1561_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1568_ = lean_unsigned_to_nat(48u);
v___x_1569_ = lean_unsigned_to_nat(2836u);
v___x_1570_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5));
v___x_1571_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_forConst_1575_, lean_object* v_key_1576_, lean_object* v_realize_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_env_1586_; uint8_t v___x_1587_; 
lean_inc(v_inst_1574_);
lean_inc_ref(v_realize_1577_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1583_, 0, v_realize_1577_);
lean_closure_set(v___f_1583_, 1, v_inst_1574_);
v___x_1584_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1585_ = lean_st_ref_get(v_a_1581_);
v_env_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1586_);
lean_dec(v___x_1585_);
v___x_1587_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1586_, v_forConst_1575_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref(v_env_1586_);
lean_dec_ref(v___f_1583_);
lean_dec_ref(v_key_1576_);
lean_dec(v_forConst_1575_);
lean_dec(v_inst_1574_);
lean_dec(v_inst_1573_);
lean_inc(v_a_1581_);
lean_inc_ref(v_a_1580_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
v___x_1588_ = lean_apply_5(v_realize_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, lean_box(0));
return v___x_1588_;
}
else
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v_toCold_1591_; lean_object* v_ref_1592_; lean_object* v_fileName_1593_; lean_object* v_fileMap_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint16_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_realize_1577_);
v___x_1589_ = 0;
v___x_1590_ = lean_io_get_num_heartbeats();
v_toCold_1591_ = lean_ctor_get(v_a_1580_, 0);
v_ref_1592_ = lean_ctor_get(v_a_1580_, 2);
v_fileName_1593_ = lean_ctor_get(v_toCold_1591_, 0);
v_fileMap_1594_ = lean_ctor_get(v_toCold_1591_, 1);
v___x_1595_ = l_Lean_Options_empty;
v___x_1596_ = lean_unsigned_to_nat(1000u);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1600_ = l_Lean_firstFrontendMacroScope;
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1594_);
lean_inc_ref(v_fileName_1593_);
v___x_1604_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1604_, 0, v_fileName_1593_);
lean_ctor_set(v___x_1604_, 1, v_fileMap_1594_);
lean_ctor_set(v___x_1604_, 2, v___x_1595_);
lean_ctor_set(v___x_1604_, 3, v___x_1596_);
lean_ctor_set(v___x_1604_, 4, v___x_1597_);
lean_ctor_set(v___x_1604_, 5, v___x_1598_);
lean_ctor_set(v___x_1604_, 6, v___x_1590_);
lean_ctor_set(v___x_1604_, 7, v___x_1599_);
lean_ctor_set(v___x_1604_, 8, v___x_1597_);
lean_ctor_set(v___x_1604_, 9, v___x_1600_);
lean_ctor_set(v___x_1604_, 10, v___x_1601_);
lean_ctor_set(v___x_1604_, 11, v___x_1603_);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_uint16_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3);
v___x_1607_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1607_, 0, v___x_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1602_);
lean_ctor_set(v___x_1607_, 2, v___x_1605_);
lean_ctor_set_uint16(v___x_1607_, sizeof(void*)*3, v___x_1606_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*3 + 2, v___x_1589_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*3 + 3, v___x_1589_);
v___x_1608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1608_, 0, v___f_1583_);
lean_closure_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1573_, v_env_1586_, v_forConst_1575_, v_key_1576_, v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1661_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1661_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1661_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1610_, v___x_1584_);
lean_dec(v_a_1610_);
if (lean_obj_tag(v___x_1614_) == 1)
{
lean_object* v_val_1615_; lean_object* v_res_x3f_1616_; lean_object* v_snap_x3f_1617_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v_snap_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_res_x3f_1616_ = lean_ctor_get(v_val_1615_, 0);
lean_inc_ref(v_res_x3f_1616_);
v_snap_x3f_1617_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snap_x3f_1617_);
lean_dec(v_val_1615_);
if (lean_obj_tag(v_snap_x3f_1617_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1652_; 
v_val_1651_ = lean_ctor_get(v_snap_x3f_1617_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_snap_x3f_1617_, 1);
v___x_1652_ = l_Lean_Syntax_getRange_x3f(v_ref_1592_, v___x_1589_);
if (lean_obj_tag(v___x_1652_) == 1)
{
lean_object* v_val_1653_; lean_object* v_start_1654_; lean_object* v_stop_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_val_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v_start_1654_ = lean_ctor_get(v_val_1653_, 0);
lean_inc(v_start_1654_);
v_stop_1655_ = lean_ctor_get(v_val_1653_, 1);
lean_inc(v_stop_1655_);
lean_dec(v_val_1653_);
lean_inc_ref_n(v_fileMap_1594_, 2);
v___x_1656_ = l_Lean_FileMap_toPosition(v_fileMap_1594_, v_start_1654_);
lean_dec(v_start_1654_);
v___x_1657_ = l_Lean_FileMap_toPosition(v_fileMap_1594_, v_stop_1655_);
lean_dec(v_stop_1655_);
v___x_1658_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1651_, v___x_1656_, v___x_1657_);
v_snap_1636_ = v___x_1658_;
v___y_1637_ = v_a_1578_;
v___y_1638_ = v_a_1579_;
v___y_1639_ = v_a_1580_;
v___y_1640_ = v_a_1581_;
goto v___jp_1635_;
}
else
{
lean_dec(v___x_1652_);
v_snap_1636_ = v_val_1651_;
v___y_1637_ = v_a_1578_;
v___y_1638_ = v_a_1579_;
v___y_1639_ = v_a_1580_;
v___y_1640_ = v_a_1581_;
goto v___jp_1635_;
}
}
else
{
lean_dec(v_snap_x3f_1617_);
v___y_1619_ = v_a_1578_;
v___y_1620_ = v_a_1579_;
v___y_1621_ = v_a_1580_;
v___y_1622_ = v_a_1581_;
goto v___jp_1618_;
}
v___jp_1618_:
{
if (lean_obj_tag(v_res_x3f_1616_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; 
lean_dec(v_inst_1574_);
v_a_1623_ = lean_ctor_get(v_res_x3f_1616_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v_res_x3f_1616_, 1);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 1);
lean_ctor_set(v___x_1612_, 0, v_a_1623_);
v___x_1625_ = v___x_1612_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v_res_x3f_1616_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_res_x3f_1616_, 1);
v___x_1628_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1627_, v_inst_1574_);
lean_dec(v_inst_1574_);
lean_dec(v_a_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_del_object(v___x_1612_);
v___x_1629_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1630_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1629_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1630_;
}
else
{
lean_object* v_val_1631_; lean_object* v___x_1633_; 
v_val_1631_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1631_);
lean_dec_ref_known(v___x_1628_, 1);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v_val_1631_);
v___x_1633_ = v___x_1612_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_val_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1601_, v_snap_1636_);
v___x_1642_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1641_, v___y_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
v___y_1619_ = v___y_1637_;
v___y_1620_ = v___y_1638_;
v___y_1621_ = v___y_1639_;
v___y_1622_ = v___y_1640_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_res_x3f_1616_);
lean_del_object(v___x_1612_);
lean_dec(v_inst_1574_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v___x_1614_);
lean_del_object(v___x_1612_);
lean_dec(v_inst_1574_);
v___x_1659_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7);
v___x_1660_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1659_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_inst_1574_);
v_a_1662_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1664_ = v___x_1609_;
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1609_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1666_ = lean_io_error_to_string(v_a_1662_);
v___x_1667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
lean_inc(v_ref_1592_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_ref_1592_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1669_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1573_ = stack[0].m_obj;
lean_object* v_inst_1574_ = stack[1].m_obj;
lean_object* v_forConst_1575_ = stack[2].m_obj;
lean_object* v_key_1576_ = stack[3].m_obj;
lean_object* v_realize_1577_ = stack[4].m_obj;
lean_object* v_a_1578_ = stack[5].m_obj;
lean_object* v_a_1579_ = stack[6].m_obj;
lean_object* v_a_1580_ = stack[7].m_obj;
lean_object* v_a_1581_ = stack[8].m_obj;
lean_object* v_res_1674_;
v_res_1674_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1573_, v_inst_1574_, v_forConst_1575_, v_key_1576_, v_realize_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
stack->m_obj
 = v_res_1674_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_forConst_1677_, lean_object* v_key_1678_, lean_object* v_realize_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1675_, v_inst_1676_, v_forConst_1677_, v_key_1678_, v_realize_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1686_, lean_object* v_vals_1687_, lean_object* v_i_1688_, lean_object* v_k_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_array_get_size(v_keys_1686_);
v___x_1691_ = lean_nat_dec_lt(v_i_1688_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec(v_i_1688_);
v___x_1692_ = lean_box(0);
return v___x_1692_;
}
else
{
lean_object* v_k_x27_1693_; uint8_t v___x_1694_; 
v_k_x27_1693_ = lean_array_fget_borrowed(v_keys_1686_, v_i_1688_);
v___x_1694_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1689_, v_k_x27_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_add(v_i_1688_, v___x_1695_);
lean_dec(v_i_1688_);
v_i_1688_ = v___x_1696_;
goto _start;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_array_fget_borrowed(v_vals_1687_, v_i_1688_);
lean_dec(v_i_1688_);
lean_inc(v___x_1698_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_i_1702_, lean_object* v_k_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1700_, v_vals_1701_, v_i_1702_, v_k_1703_);
lean_dec_ref(v_k_1703_);
lean_dec_ref(v_vals_1701_);
lean_dec_ref(v_keys_1700_);
return v_res_1704_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1705_, size_t v_x_1706_, lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_es_1708_; lean_object* v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v_j_1712_; lean_object* v___x_1713_; 
v_es_1708_ = lean_ctor_get(v_x_1705_, 0);
v___x_1709_ = lean_box(2);
v___x_1710_ = ((size_t)31ULL);
v___x_1711_ = lean_usize_land(v_x_1706_, v___x_1710_);
v_j_1712_ = lean_usize_to_nat(v___x_1711_);
v___x_1713_ = lean_array_get_borrowed(v___x_1709_, v_es_1708_, v_j_1712_);
lean_dec(v_j_1712_);
switch(lean_obj_tag(v___x_1713_))
{
case 0:
{
lean_object* v_key_1714_; lean_object* v_val_1715_; uint8_t v___x_1716_; 
v_key_1714_ = lean_ctor_get(v___x_1713_, 0);
v_val_1715_ = lean_ctor_get(v___x_1713_, 1);
v___x_1716_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1707_, v_key_1714_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; 
lean_inc(v_val_1715_);
v___x_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_val_1715_);
return v___x_1718_;
}
}
case 1:
{
lean_object* v_node_1719_; size_t v___x_1720_; size_t v___x_1721_; 
v_node_1719_ = lean_ctor_get(v___x_1713_, 0);
v___x_1720_ = ((size_t)5ULL);
v___x_1721_ = lean_usize_shift_right(v_x_1706_, v___x_1720_);
v_x_1705_ = v_node_1719_;
v_x_1706_ = v___x_1721_;
goto _start;
}
default: 
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_box(0);
return v___x_1723_;
}
}
}
else
{
lean_object* v_ks_1724_; lean_object* v_vs_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_ks_1724_ = lean_ctor_get(v_x_1705_, 0);
v_vs_1725_ = lean_ctor_get(v_x_1705_, 1);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1724_, v_vs_1725_, v___x_1726_, v_x_1707_);
return v___x_1727_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1705_ = stack[0].m_obj;
size_t v_x_1706_ = stack[1].m_num;
lean_object* v_x_1707_ = stack[2].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1705_, v_x_1706_, v_x_1707_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
size_t v_x_13359__boxed_1732_; lean_object* v_res_1733_; 
v_x_13359__boxed_1732_ = lean_unbox_usize(v_x_1730_);
lean_dec(v_x_1730_);
v_res_1733_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1729_, v_x_13359__boxed_1732_, v_x_1731_);
lean_dec_ref(v_x_1731_);
lean_dec_ref(v_x_1729_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
uint64_t v_configKey_1736_; lean_object* v_expr_1737_; lean_object* v_nargs_x3f_1738_; uint64_t v___x_1739_; uint64_t v___y_1741_; 
v_configKey_1736_ = lean_ctor_get_uint64(v_x_1735_, sizeof(void*)*2);
v_expr_1737_ = lean_ctor_get(v_x_1735_, 0);
v_nargs_x3f_1738_ = lean_ctor_get(v_x_1735_, 1);
v___x_1739_ = l_Lean_Expr_hash(v_expr_1737_);
if (lean_obj_tag(v_nargs_x3f_1738_) == 0)
{
uint64_t v___x_1746_; 
v___x_1746_ = 11ULL;
v___y_1741_ = v___x_1746_;
goto v___jp_1740_;
}
else
{
lean_object* v_val_1747_; uint64_t v___x_1748_; uint64_t v___x_1749_; uint64_t v___x_1750_; 
v_val_1747_ = lean_ctor_get(v_nargs_x3f_1738_, 0);
v___x_1748_ = lean_uint64_of_nat(v_val_1747_);
v___x_1749_ = 13ULL;
v___x_1750_ = lean_uint64_mix_hash(v___x_1748_, v___x_1749_);
v___y_1741_ = v___x_1750_;
goto v___jp_1740_;
}
v___jp_1740_:
{
uint64_t v___x_1742_; uint64_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = lean_uint64_mix_hash(v___x_1739_, v___y_1741_);
v___x_1743_ = lean_uint64_mix_hash(v_configKey_1736_, v___x_1742_);
v___x_1744_ = lean_uint64_to_usize(v___x_1743_);
v___x_1745_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1734_, v___x_1744_, v_x_1735_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1751_, v_x_1752_);
lean_dec_ref(v_x_1752_);
lean_dec_ref(v_x_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v_ks_1758_; lean_object* v_vs_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1783_; 
v_ks_1758_ = lean_ctor_get(v_x_1754_, 0);
v_vs_1759_ = lean_ctor_get(v_x_1754_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_x_1754_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1761_ = v_x_1754_;
v_isShared_1762_ = v_isSharedCheck_1783_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_vs_1759_);
lean_inc(v_ks_1758_);
lean_dec(v_x_1754_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1783_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_array_get_size(v_ks_1758_);
v___x_1764_ = lean_nat_dec_lt(v_x_1755_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v_x_1755_);
v___x_1765_ = lean_array_push(v_ks_1758_, v_x_1756_);
v___x_1766_ = lean_array_push(v_vs_1759_, v_x_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1766_);
lean_ctor_set(v___x_1761_, 0, v___x_1765_);
v___x_1768_ = v___x_1761_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
else
{
lean_object* v_k_x27_1770_; uint8_t v___x_1771_; 
v_k_x27_1770_ = lean_array_fget_borrowed(v_ks_1758_, v_x_1755_);
v___x_1771_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1756_, v_k_x27_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1773_; 
if (v_isShared_1762_ == 0)
{
v___x_1773_ = v___x_1761_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_ks_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_vs_1759_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_x_1755_, v___x_1774_);
lean_dec(v_x_1755_);
v_x_1754_ = v___x_1773_;
v_x_1755_ = v___x_1775_;
goto _start;
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_array_fset(v_ks_1758_, v_x_1755_, v_x_1756_);
v___x_1779_ = lean_array_fset(v_vs_1759_, v_x_1755_, v_x_1757_);
lean_dec(v_x_1755_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1779_);
lean_ctor_set(v___x_1761_, 0, v___x_1778_);
v___x_1781_ = v___x_1761_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1784_, lean_object* v_k_1785_, lean_object* v_v_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1784_, v___x_1787_, v_k_1785_, v_v_1786_);
return v___x_1788_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1789_, size_t v_x_1790_, size_t v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v_es_1794_; size_t v___x_1795_; size_t v___x_1796_; lean_object* v_j_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_es_1794_ = lean_ctor_get(v_x_1789_, 0);
v___x_1795_ = ((size_t)31ULL);
v___x_1796_ = lean_usize_land(v_x_1790_, v___x_1795_);
v_j_1797_ = lean_usize_to_nat(v___x_1796_);
v___x_1798_ = lean_array_get_size(v_es_1794_);
v___x_1799_ = lean_nat_dec_lt(v_j_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec(v_j_1797_);
lean_dec(v_x_1793_);
lean_dec_ref(v_x_1792_);
return v_x_1789_;
}
else
{
lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1838_; 
lean_inc_ref(v_es_1794_);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v_x_1789_, 0);
lean_dec(v_unused_1839_);
v___x_1801_ = v_x_1789_;
v_isShared_1802_ = v_isSharedCheck_1838_;
goto v_resetjp_1800_;
}
else
{
lean_dec(v_x_1789_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1838_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_v_1803_; lean_object* v___x_1804_; lean_object* v_xs_x27_1805_; lean_object* v___y_1807_; 
v_v_1803_ = lean_array_fget(v_es_1794_, v_j_1797_);
v___x_1804_ = lean_box(0);
v_xs_x27_1805_ = lean_array_fset(v_es_1794_, v_j_1797_, v___x_1804_);
switch(lean_obj_tag(v_v_1803_))
{
case 0:
{
lean_object* v_key_1812_; lean_object* v_val_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_key_1812_ = lean_ctor_get(v_v_1803_, 0);
v_val_1813_ = lean_ctor_get(v_v_1803_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_v_1803_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v_v_1803_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_val_1813_);
lean_inc(v_key_1812_);
lean_dec(v_v_1803_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1792_, v_key_1812_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1815_);
v___x_1818_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1812_, v_val_1813_, v_x_1792_, v_x_1793_);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
v___y_1807_ = v___x_1819_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_val_1813_);
lean_dec(v_key_1812_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v_x_1793_);
lean_ctor_set(v___x_1815_, 0, v_x_1792_);
v___x_1821_ = v___x_1815_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_x_1792_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_x_1793_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v___y_1807_ = v___x_1821_;
goto v___jp_1806_;
}
}
}
}
case 1:
{
lean_object* v_node_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1836_; 
v_node_1824_ = lean_ctor_get(v_v_1803_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_v_1803_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1826_ = v_v_1803_;
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_node_1824_);
lean_dec(v_v_1803_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
size_t v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1828_ = ((size_t)5ULL);
v___x_1829_ = lean_usize_shift_right(v_x_1790_, v___x_1828_);
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_x_1791_, v___x_1830_);
v___x_1832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1824_, v___x_1829_, v___x_1831_, v_x_1792_, v_x_1793_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1832_);
v___x_1834_ = v___x_1826_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v___y_1807_ = v___x_1834_;
goto v___jp_1806_;
}
}
}
default: 
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_x_1792_);
lean_ctor_set(v___x_1837_, 1, v_x_1793_);
v___y_1807_ = v___x_1837_;
goto v___jp_1806_;
}
}
v___jp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_array_fset(v_xs_x27_1805_, v_j_1797_, v___y_1807_);
lean_dec(v_j_1797_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1808_);
v___x_1810_ = v___x_1801_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
else
{
lean_object* v_ks_1840_; lean_object* v_vs_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1859_; 
v_ks_1840_ = lean_ctor_get(v_x_1789_, 0);
v_vs_1841_ = lean_ctor_get(v_x_1789_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1843_ = v_x_1789_;
v_isShared_1844_ = v_isSharedCheck_1859_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_vs_1841_);
lean_inc(v_ks_1840_);
lean_dec(v_x_1789_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1859_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_ks_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_vs_1841_);
v___x_1846_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v_newNode_1847_; size_t v___x_1848_; uint8_t v___x_1849_; 
v_newNode_1847_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1846_, v_x_1792_, v_x_1793_);
v___x_1848_ = ((size_t)7ULL);
v___x_1849_ = lean_usize_dec_le(v___x_1848_, v_x_1791_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1850_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1847_);
v___x_1851_ = lean_unsigned_to_nat(4u);
v___x_1852_ = lean_nat_dec_lt(v___x_1850_, v___x_1851_);
lean_dec(v___x_1850_);
if (v___x_1852_ == 0)
{
lean_object* v_ks_1853_; lean_object* v_vs_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_ks_1853_ = lean_ctor_get(v_newNode_1847_, 0);
lean_inc_ref(v_ks_1853_);
v_vs_1854_ = lean_ctor_get(v_newNode_1847_, 1);
lean_inc_ref(v_vs_1854_);
lean_dec_ref(v_newNode_1847_);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1791_, v_ks_1853_, v_vs_1854_, v___x_1855_, v___x_1856_);
lean_dec_ref(v_vs_1854_);
lean_dec_ref(v_ks_1853_);
return v___x_1857_;
}
else
{
return v_newNode_1847_;
}
}
else
{
return v_newNode_1847_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1789_ = stack[0].m_obj;
size_t v_x_1790_ = stack[1].m_num;
size_t v_x_1791_ = stack[2].m_num;
lean_object* v_x_1792_ = stack[3].m_obj;
lean_object* v_x_1793_ = stack[4].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1789_, v_x_1790_, v_x_1791_, v_x_1792_, v_x_1793_);
stack->m_obj
 = v_res_1860_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1861_, lean_object* v_keys_1862_, lean_object* v_vals_1863_, lean_object* v_i_1864_, lean_object* v_entries_1865_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_array_get_size(v_keys_1862_);
v___x_1867_ = lean_nat_dec_lt(v_i_1864_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec(v_i_1864_);
return v_entries_1865_;
}
else
{
lean_object* v_k_1868_; uint64_t v_configKey_1869_; lean_object* v_expr_1870_; lean_object* v_nargs_x3f_1871_; lean_object* v_v_1872_; uint64_t v___x_1873_; uint64_t v___y_1875_; 
v_k_1868_ = lean_array_fget_borrowed(v_keys_1862_, v_i_1864_);
v_configKey_1869_ = lean_ctor_get_uint64(v_k_1868_, sizeof(void*)*2);
v_expr_1870_ = lean_ctor_get(v_k_1868_, 0);
v_nargs_x3f_1871_ = lean_ctor_get(v_k_1868_, 1);
v_v_1872_ = lean_array_fget_borrowed(v_vals_1863_, v_i_1864_);
v___x_1873_ = l_Lean_Expr_hash(v_expr_1870_);
if (lean_obj_tag(v_nargs_x3f_1871_) == 0)
{
uint64_t v___x_1888_; 
v___x_1888_ = 11ULL;
v___y_1875_ = v___x_1888_;
goto v___jp_1874_;
}
else
{
lean_object* v_val_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; 
v_val_1889_ = lean_ctor_get(v_nargs_x3f_1871_, 0);
v___x_1890_ = lean_uint64_of_nat(v_val_1889_);
v___x_1891_ = 13ULL;
v___x_1892_ = lean_uint64_mix_hash(v___x_1890_, v___x_1891_);
v___y_1875_ = v___x_1892_;
goto v___jp_1874_;
}
v___jp_1874_:
{
uint64_t v___x_1876_; uint64_t v___x_1877_; size_t v_h_1878_; size_t v___x_1879_; lean_object* v___x_1880_; size_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v_h_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1876_ = lean_uint64_mix_hash(v___x_1873_, v___y_1875_);
v___x_1877_ = lean_uint64_mix_hash(v_configKey_1869_, v___x_1876_);
v_h_1878_ = lean_uint64_to_usize(v___x_1877_);
v___x_1879_ = ((size_t)5ULL);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_sub(v_depth_1861_, v___x_1881_);
v___x_1883_ = lean_usize_mul(v___x_1879_, v___x_1882_);
v_h_1884_ = lean_usize_shift_right(v_h_1878_, v___x_1883_);
v___x_1885_ = lean_nat_add(v_i_1864_, v___x_1880_);
lean_dec(v_i_1864_);
lean_inc(v_v_1872_);
lean_inc(v_k_1868_);
v___x_1886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1865_, v_h_1884_, v_depth_1861_, v_k_1868_, v_v_1872_);
v_i_1864_ = v___x_1885_;
v_entries_1865_ = v___x_1886_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1861_ = stack[0].m_num;
lean_object* v_keys_1862_ = stack[1].m_obj;
lean_object* v_vals_1863_ = stack[2].m_obj;
lean_object* v_i_1864_ = stack[3].m_obj;
lean_object* v_entries_1865_ = stack[4].m_obj;
lean_object* v_res_1893_;
v_res_1893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_1861_, v_keys_1862_, v_vals_1863_, v_i_1864_, v_entries_1865_);
stack->m_obj
 = v_res_1893_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1894_, lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_entries_1898_){
_start:
{
size_t v_depth_boxed_1899_; lean_object* v_res_1900_; 
v_depth_boxed_1899_ = lean_unbox_usize(v_depth_1894_);
lean_dec(v_depth_1894_);
v_res_1900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1899_, v_keys_1895_, v_vals_1896_, v_i_1897_, v_entries_1898_);
lean_dec_ref(v_vals_1896_);
lean_dec_ref(v_keys_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
size_t v_x_13604__boxed_1906_; size_t v_x_13605__boxed_1907_; lean_object* v_res_1908_; 
v_x_13604__boxed_1906_ = lean_unbox_usize(v_x_1902_);
lean_dec(v_x_1902_);
v_x_13605__boxed_1907_ = lean_unbox_usize(v_x_1903_);
lean_dec(v_x_1903_);
v_res_1908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1901_, v_x_13604__boxed_1906_, v_x_13605__boxed_1907_, v_x_1904_, v_x_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
uint64_t v_configKey_1912_; lean_object* v_expr_1913_; lean_object* v_nargs_x3f_1914_; uint64_t v___x_1915_; uint64_t v___y_1917_; 
v_configKey_1912_ = lean_ctor_get_uint64(v_x_1910_, sizeof(void*)*2);
v_expr_1913_ = lean_ctor_get(v_x_1910_, 0);
v_nargs_x3f_1914_ = lean_ctor_get(v_x_1910_, 1);
v___x_1915_ = l_Lean_Expr_hash(v_expr_1913_);
if (lean_obj_tag(v_nargs_x3f_1914_) == 0)
{
uint64_t v___x_1923_; 
v___x_1923_ = 11ULL;
v___y_1917_ = v___x_1923_;
goto v___jp_1916_;
}
else
{
lean_object* v_val_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; 
v_val_1924_ = lean_ctor_get(v_nargs_x3f_1914_, 0);
v___x_1925_ = lean_uint64_of_nat(v_val_1924_);
v___x_1926_ = 13ULL;
v___x_1927_ = lean_uint64_mix_hash(v___x_1925_, v___x_1926_);
v___y_1917_ = v___x_1927_;
goto v___jp_1916_;
}
v___jp_1916_:
{
uint64_t v___x_1918_; uint64_t v___x_1919_; size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1918_ = lean_uint64_mix_hash(v___x_1915_, v___y_1917_);
v___x_1919_ = lean_uint64_mix_hash(v_configKey_1912_, v___x_1918_);
v___x_1920_ = lean_uint64_to_usize(v___x_1919_);
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1909_, v___x_1920_, v___x_1921_, v_x_1910_, v_x_1911_);
return v___x_1922_;
}
}
}
uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = 0;
return v___x_1929_;
}
else
{
lean_object* v_head_1930_; lean_object* v_tail_1931_; uint8_t v___x_1932_; 
v_head_1930_ = lean_ctor_get(v_x_1928_, 0);
v_tail_1931_ = lean_ctor_get(v_x_1928_, 1);
v___x_1932_ = l_Lean_Level_hasMVar(v_head_1930_);
if (v___x_1932_ == 0)
{
v_x_1928_ = v_tail_1931_;
goto _start;
}
else
{
return v___x_1932_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1928_ = stack[0].m_obj;
uint8_t v_res_1934_;
v_res_1934_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1928_);
stack->m_num = v_res_1934_;
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1935_){
_start:
{
uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1935_);
lean_dec(v_x_1935_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1940_, lean_object* v_maxArgs_x3f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___f_1947_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc_n(v_maxArgs_x3f_1941_, 2);
lean_inc_ref_n(v_fn_1940_, 2);
v___f_1948_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1948_, 0, v_fn_1940_);
lean_closure_set(v___f_1948_, 1, v_maxArgs_x3f_1941_);
lean_closure_set(v___f_1948_, 2, v___f_1947_);
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_1950_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_1951_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1940_, v_maxArgs_x3f_1941_, v_a_1942_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2012_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_2012_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2012_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_finfo_1957_; lean_object* v___y_1958_; lean_object* v___x_1990_; lean_object* v_cache_1991_; lean_object* v_funInfo_1992_; lean_object* v___x_1993_; 
v___x_1990_ = lean_st_ref_get(v_a_1943_);
v_cache_1991_ = lean_ctor_get(v___x_1990_, 1);
lean_inc_ref(v_cache_1991_);
lean_dec(v___x_1990_);
v_funInfo_1992_ = lean_ctor_get(v_cache_1991_, 1);
lean_inc_ref(v_funInfo_1992_);
lean_dec_ref(v_cache_1991_);
v___x_1993_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1992_, v_a_1952_);
lean_dec_ref(v_funInfo_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
if (lean_obj_tag(v_fn_1940_) == 4)
{
lean_object* v_declName_1994_; lean_object* v_us_1995_; uint8_t v___x_1996_; 
v_declName_1994_ = lean_ctor_get(v_fn_1940_, 0);
v_us_1995_ = lean_ctor_get(v_fn_1940_, 1);
v___x_1996_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc(v_us_1995_);
lean_inc_n(v_declName_1994_, 2);
lean_dec_ref_known(v_fn_1940_, 2);
v___x_1997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1997_, 0, v_declName_1994_);
lean_ctor_set(v___x_1997_, 1, v_us_1995_);
lean_ctor_set(v___x_1997_, 2, v_maxArgs_x3f_1941_);
v___x_1998_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_1949_, v___x_1950_, v_declName_1994_, v___x_1997_, v___f_1948_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_finfo_1957_ = v_a_1999_;
v___y_1958_ = v_a_1943_;
goto v___jp_1956_;
}
else
{
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
return v___x_1998_;
}
}
else
{
lean_object* v___x_2000_; 
lean_dec_ref(v___f_1948_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2000_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1940_, v_maxArgs_x3f_1941_, v___f_1947_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v_finfo_1957_ = v_a_2001_;
v___y_1958_ = v_a_1943_;
goto v___jp_1956_;
}
else
{
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
return v___x_2000_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec_ref(v___f_1948_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2002_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1940_, v_maxArgs_x3f_1941_, v___f_1947_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v_finfo_1957_ = v_a_2003_;
v___y_1958_ = v_a_1943_;
goto v___jp_1956_;
}
else
{
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
return v___x_2002_;
}
}
}
else
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
lean_dec_ref(v___f_1948_);
lean_dec(v_maxArgs_x3f_1941_);
lean_dec_ref(v_fn_1940_);
v_val_2004_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1993_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_1993_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 0);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
v___jp_1956_:
{
lean_object* v___x_1959_; lean_object* v_cache_1960_; lean_object* v_mctx_1961_; lean_object* v_zetaDeltaFVarIds_1962_; lean_object* v_postponed_1963_; lean_object* v_diag_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1989_; 
v___x_1959_ = lean_st_ref_take(v___y_1958_);
v_cache_1960_ = lean_ctor_get(v___x_1959_, 1);
v_mctx_1961_ = lean_ctor_get(v___x_1959_, 0);
v_zetaDeltaFVarIds_1962_ = lean_ctor_get(v___x_1959_, 2);
v_postponed_1963_ = lean_ctor_get(v___x_1959_, 3);
v_diag_1964_ = lean_ctor_get(v___x_1959_, 4);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1966_ = v___x_1959_;
v_isShared_1967_ = v_isSharedCheck_1989_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_diag_1964_);
lean_inc(v_postponed_1963_);
lean_inc(v_zetaDeltaFVarIds_1962_);
lean_inc(v_cache_1960_);
lean_inc(v_mctx_1961_);
lean_dec(v___x_1959_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1989_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_inferType_1968_; lean_object* v_funInfo_1969_; lean_object* v_synthInstance_1970_; lean_object* v_whnf_1971_; lean_object* v_defEqTrans_1972_; lean_object* v_defEqPerm_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1988_; 
v_inferType_1968_ = lean_ctor_get(v_cache_1960_, 0);
v_funInfo_1969_ = lean_ctor_get(v_cache_1960_, 1);
v_synthInstance_1970_ = lean_ctor_get(v_cache_1960_, 2);
v_whnf_1971_ = lean_ctor_get(v_cache_1960_, 3);
v_defEqTrans_1972_ = lean_ctor_get(v_cache_1960_, 4);
v_defEqPerm_1973_ = lean_ctor_get(v_cache_1960_, 5);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_cache_1960_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1975_ = v_cache_1960_;
v_isShared_1976_ = v_isSharedCheck_1988_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_defEqPerm_1973_);
lean_inc(v_defEqTrans_1972_);
lean_inc(v_whnf_1971_);
lean_inc(v_synthInstance_1970_);
lean_inc(v_funInfo_1969_);
lean_inc(v_inferType_1968_);
lean_dec(v_cache_1960_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1988_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
lean_inc_ref(v_finfo_1957_);
v___x_1977_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1969_, v_a_1952_, v_finfo_1957_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_inferType_1968_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_synthInstance_1970_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_whnf_1971_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_defEqTrans_1972_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v_defEqPerm_1973_);
v___x_1979_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___x_1979_);
v___x_1981_ = v___x_1966_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_mctx_1961_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_zetaDeltaFVarIds_1962_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_postponed_1963_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_diag_1964_);
v___x_1981_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_st_ref_put(v___y_1958_, v___x_1981_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v_finfo_1957_);
v___x_1984_ = v___x_1954_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_finfo_1957_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
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
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v___f_1948_);
lean_dec(v_maxArgs_x3f_1941_);
lean_dec_ref(v_fn_1940_);
v_a_2013_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1951_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1951_);
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
LEAN_EXPORT void l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1940_ = stack[0].m_obj;
lean_object* v_maxArgs_x3f_1941_ = stack[1].m_obj;
lean_object* v_a_1942_ = stack[2].m_obj;
lean_object* v_a_1943_ = stack[3].m_obj;
lean_object* v_a_1944_ = stack[4].m_obj;
lean_object* v_a_1945_ = stack[5].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_1940_, v_maxArgs_x3f_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_2022_, lean_object* v_maxArgs_x3f_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2022_, v_maxArgs_x3f_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
return v_res_2029_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_2030_, lean_object* v_k_2031_, lean_object* v_t_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_2031_, v_t_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2031_ = stack[1].m_obj;
lean_object* v_t_2032_ = stack[2].m_obj;
uint8_t v_res_2034_;
v_res_2034_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_box(0), v_k_2031_, v_t_2032_);
stack->m_num = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2035_, lean_object* v_k_2036_, lean_object* v_t_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2035_, v_k_2036_, v_t_2037_);
lean_dec(v_t_2037_);
lean_dec(v_k_2036_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2040_, lean_object* v_val_2041_, lean_object* v___x_2042_, lean_object* v_fvars_2043_, lean_object* v_next_2044_, lean_object* v_upperBound_2045_, lean_object* v_inst_2046_, lean_object* v_R_2047_, lean_object* v_a_2048_, lean_object* v_b_2049_, lean_object* v_c_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2040_, v_val_2041_, v___x_2042_, v_fvars_2043_, v_next_2044_, v_upperBound_2045_, v_a_2048_, v_b_2049_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
return v___x_2056_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2040_ = stack[0].m_obj;
lean_object* v_val_2041_ = stack[1].m_obj;
lean_object* v___x_2042_ = stack[2].m_obj;
lean_object* v_fvars_2043_ = stack[3].m_obj;
lean_object* v_next_2044_ = stack[4].m_obj;
lean_object* v_upperBound_2045_ = stack[5].m_obj;
lean_object* v_a_2048_ = stack[8].m_obj;
lean_object* v_b_2049_ = stack[9].m_obj;
lean_object* v___y_2051_ = stack[11].m_obj;
lean_object* v___y_2052_ = stack[12].m_obj;
lean_object* v___y_2053_ = stack[13].m_obj;
lean_object* v___y_2054_ = stack[14].m_obj;
lean_object* v_res_2057_;
v_res_2057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2040_, v_val_2041_, v___x_2042_, v_fvars_2043_, v_next_2044_, v_upperBound_2045_, lean_box(0), lean_box(0), v_a_2048_, v_b_2049_, lean_box(0), v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
stack->m_obj
 = v_res_2057_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2058_, lean_object* v_val_2059_, lean_object* v___x_2060_, lean_object* v_fvars_2061_, lean_object* v_next_2062_, lean_object* v_upperBound_2063_, lean_object* v_inst_2064_, lean_object* v_R_2065_, lean_object* v_a_2066_, lean_object* v_b_2067_, lean_object* v_c_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2058_, v_val_2059_, v___x_2060_, v_fvars_2061_, v_next_2062_, v_upperBound_2063_, v_inst_2064_, v_R_2065_, v_a_2066_, v_b_2067_, v_c_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_upperBound_2063_);
lean_dec(v_next_2062_);
lean_dec_ref(v_fvars_2061_);
lean_dec_ref(v___x_2060_);
lean_dec_ref(v_val_2059_);
lean_dec(v_upperBound_2058_);
return v_res_2074_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2075_, lean_object* v_fvars_2076_, lean_object* v_inst_2077_, lean_object* v_R_2078_, lean_object* v_a_2079_, lean_object* v_b_2080_, lean_object* v_c_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2075_, v_fvars_2076_, v_a_2079_, v_b_2080_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2075_ = stack[0].m_obj;
lean_object* v_fvars_2076_ = stack[1].m_obj;
lean_object* v_a_2079_ = stack[4].m_obj;
lean_object* v_b_2080_ = stack[5].m_obj;
lean_object* v___y_2082_ = stack[7].m_obj;
lean_object* v___y_2083_ = stack[8].m_obj;
lean_object* v___y_2084_ = stack[9].m_obj;
lean_object* v___y_2085_ = stack[10].m_obj;
lean_object* v_res_2088_;
v_res_2088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2075_, v_fvars_2076_, lean_box(0), lean_box(0), v_a_2079_, v_b_2080_, lean_box(0), v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2088_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2089_, lean_object* v_fvars_2090_, lean_object* v_inst_2091_, lean_object* v_R_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_, lean_object* v_c_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2089_, v_fvars_2090_, v_inst_2091_, v_R_2092_, v_a_2093_, v_b_2094_, v_c_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_fvars_2090_);
lean_dec(v_upperBound_2089_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2103_, v_x_2104_, v_x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2108_, v_x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2111_, v_x_2112_, v_x_2113_);
lean_dec_ref(v_x_2113_);
lean_dec_ref(v_x_2112_);
return v_res_2114_;
}
}
lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2115_, lean_object* v_msg_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2116_ = stack[1].m_obj;
lean_object* v___y_2117_ = stack[2].m_obj;
lean_object* v___y_2118_ = stack[3].m_obj;
lean_object* v___y_2119_ = stack[4].m_obj;
lean_object* v___y_2120_ = stack[5].m_obj;
lean_object* v_res_2123_;
v_res_2123_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_box(0), v_msg_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
stack->m_obj
 = v_res_2123_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2124_, lean_object* v_msg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2124_, v_msg_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2131_;
}
}
lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_forConst_2135_, lean_object* v_key_2136_, lean_object* v_realize_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2133_, v_inst_2134_, v_forConst_2135_, v_key_2136_, v_realize_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT void l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2133_ = stack[1].m_obj;
lean_object* v_inst_2134_ = stack[2].m_obj;
lean_object* v_forConst_2135_ = stack[3].m_obj;
lean_object* v_key_2136_ = stack[4].m_obj;
lean_object* v_realize_2137_ = stack[5].m_obj;
lean_object* v_a_2138_ = stack[6].m_obj;
lean_object* v_a_2139_ = stack[7].m_obj;
lean_object* v_a_2140_ = stack[8].m_obj;
lean_object* v_a_2141_ = stack[9].m_obj;
lean_object* v_res_2144_;
v_res_2144_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_box(0), v_inst_2133_, v_inst_2134_, v_forConst_2135_, v_key_2136_, v_realize_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
stack->m_obj
 = v_res_2144_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_forConst_2148_, lean_object* v_key_2149_, lean_object* v_realize_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2145_, v_inst_2146_, v_inst_2147_, v_forConst_2148_, v_key_2149_, v_realize_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
return v_res_2156_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2157_, lean_object* v_x_2158_, size_t v_x_2159_, size_t v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2158_, v_x_2159_, v_x_2160_, v_x_2161_, v_x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2158_ = stack[1].m_obj;
size_t v_x_2159_ = stack[2].m_num;
size_t v_x_2160_ = stack[3].m_num;
lean_object* v_x_2161_ = stack[4].m_obj;
lean_object* v_x_2162_ = stack[5].m_obj;
lean_object* v_res_2164_;
v_res_2164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_box(0), v_x_2158_, v_x_2159_, v_x_2160_, v_x_2161_, v_x_2162_);
stack->m_obj
 = v_res_2164_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
size_t v_x_14300__boxed_2171_; size_t v_x_14301__boxed_2172_; lean_object* v_res_2173_; 
v_x_14300__boxed_2171_ = lean_unbox_usize(v_x_2167_);
lean_dec(v_x_2167_);
v_x_14301__boxed_2172_ = lean_unbox_usize(v_x_2168_);
lean_dec(v_x_2168_);
v_res_2173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2165_, v_x_2166_, v_x_14300__boxed_2171_, v_x_14301__boxed_2172_, v_x_2169_, v_x_2170_);
return v_res_2173_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2174_, lean_object* v_x_2175_, size_t v_x_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2175_, v_x_2176_, v_x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2175_ = stack[1].m_obj;
size_t v_x_2176_ = stack[2].m_num;
lean_object* v_x_2177_ = stack[3].m_obj;
lean_object* v_res_2179_;
v_res_2179_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_box(0), v_x_2175_, v_x_2176_, v_x_2177_);
stack->m_obj
 = v_res_2179_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
size_t v_x_14328__boxed_2184_; lean_object* v_res_2185_; 
v_x_14328__boxed_2184_ = lean_unbox_usize(v_x_2182_);
lean_dec(v_x_2182_);
v_res_2185_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2180_, v_x_2181_, v_x_14328__boxed_2184_, v_x_2183_);
lean_dec_ref(v_x_2183_);
lean_dec_ref(v_x_2181_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2186_, lean_object* v_n_2187_, lean_object* v_k_2188_, lean_object* v_v_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2187_, v_k_2188_, v_v_2189_);
return v___x_2190_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2191_, size_t v_depth_2192_, lean_object* v_keys_2193_, lean_object* v_vals_2194_, lean_object* v_heq_2195_, lean_object* v_i_2196_, lean_object* v_entries_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2192_, v_keys_2193_, v_vals_2194_, v_i_2196_, v_entries_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2192_ = stack[1].m_num;
lean_object* v_keys_2193_ = stack[2].m_obj;
lean_object* v_vals_2194_ = stack[3].m_obj;
lean_object* v_i_2196_ = stack[5].m_obj;
lean_object* v_entries_2197_ = stack[6].m_obj;
lean_object* v_res_2199_;
v_res_2199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_box(0), v_depth_2192_, v_keys_2193_, v_vals_2194_, lean_box(0), v_i_2196_, v_entries_2197_);
stack->m_obj
 = v_res_2199_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2200_, lean_object* v_depth_2201_, lean_object* v_keys_2202_, lean_object* v_vals_2203_, lean_object* v_heq_2204_, lean_object* v_i_2205_, lean_object* v_entries_2206_){
_start:
{
size_t v_depth_boxed_2207_; lean_object* v_res_2208_; 
v_depth_boxed_2207_ = lean_unbox_usize(v_depth_2201_);
lean_dec(v_depth_2201_);
v_res_2208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2200_, v_depth_boxed_2207_, v_keys_2202_, v_vals_2203_, v_heq_2204_, v_i_2205_, v_entries_2206_);
lean_dec_ref(v_vals_2203_);
lean_dec_ref(v_keys_2202_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2209_, lean_object* v_keys_2210_, lean_object* v_vals_2211_, lean_object* v_heq_2212_, lean_object* v_i_2213_, lean_object* v_k_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2210_, v_vals_2211_, v_i_2213_, v_k_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_keys_2217_, lean_object* v_vals_2218_, lean_object* v_heq_2219_, lean_object* v_i_2220_, lean_object* v_k_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2216_, v_keys_2217_, v_vals_2218_, v_heq_2219_, v_i_2220_, v_k_2221_);
lean_dec_ref(v_k_2221_);
lean_dec_ref(v_vals_2218_);
lean_dec_ref(v_keys_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2227_, v_x_2228_, v_x_2229_);
lean_dec_ref(v_x_2229_);
lean_dec_ref(v_x_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2237_, v_x_2238_, v_x_2239_, v_x_2240_);
return v___x_2241_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2242_, lean_object* v_x_2243_, size_t v_x_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2243_, v_x_2244_, v_x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2243_ = stack[1].m_obj;
size_t v_x_2244_ = stack[2].m_num;
lean_object* v_x_2245_ = stack[3].m_obj;
lean_object* v_res_2247_;
v_res_2247_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_box(0), v_x_2243_, v_x_2244_, v_x_2245_);
stack->m_obj
 = v_res_2247_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
size_t v_x_14395__boxed_2252_; lean_object* v_res_2253_; 
v_x_14395__boxed_2252_ = lean_unbox_usize(v_x_2250_);
lean_dec(v_x_2250_);
v_res_2253_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2248_, v_x_2249_, v_x_14395__boxed_2252_, v_x_2251_);
lean_dec_ref(v_x_2251_);
lean_dec_ref(v_x_2249_);
return v_res_2253_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2254_, lean_object* v_x_2255_, size_t v_x_2256_, size_t v_x_2257_, lean_object* v_x_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2255_, v_x_2256_, v_x_2257_, v_x_2258_, v_x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2255_ = stack[1].m_obj;
size_t v_x_2256_ = stack[2].m_num;
size_t v_x_2257_ = stack[3].m_num;
lean_object* v_x_2258_ = stack[4].m_obj;
lean_object* v_x_2259_ = stack[5].m_obj;
lean_object* v_res_2261_;
v_res_2261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_box(0), v_x_2255_, v_x_2256_, v_x_2257_, v_x_2258_, v_x_2259_);
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
size_t v_x_14413__boxed_2268_; size_t v_x_14414__boxed_2269_; lean_object* v_res_2270_; 
v_x_14413__boxed_2268_ = lean_unbox_usize(v_x_2264_);
lean_dec(v_x_2264_);
v_x_14414__boxed_2269_ = lean_unbox_usize(v_x_2265_);
lean_dec(v_x_2265_);
v_res_2270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2262_, v_x_2263_, v_x_14413__boxed_2268_, v_x_14414__boxed_2269_, v_x_2266_, v_x_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2271_, lean_object* v_keys_2272_, lean_object* v_vals_2273_, lean_object* v_heq_2274_, lean_object* v_i_2275_, lean_object* v_k_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2272_, v_vals_2273_, v_i_2275_, v_k_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2278_, lean_object* v_keys_2279_, lean_object* v_vals_2280_, lean_object* v_heq_2281_, lean_object* v_i_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2278_, v_keys_2279_, v_vals_2280_, v_heq_2281_, v_i_2282_, v_k_2283_);
lean_dec_ref(v_k_2283_);
lean_dec_ref(v_vals_2280_);
lean_dec_ref(v_keys_2279_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2285_, lean_object* v_n_2286_, lean_object* v_k_2287_, lean_object* v_v_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2286_, v_k_2287_, v_v_2288_);
return v___x_2289_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2290_, size_t v_depth_2291_, lean_object* v_keys_2292_, lean_object* v_vals_2293_, lean_object* v_heq_2294_, lean_object* v_i_2295_, lean_object* v_entries_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2291_, v_keys_2292_, v_vals_2293_, v_i_2295_, v_entries_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2291_ = stack[1].m_num;
lean_object* v_keys_2292_ = stack[2].m_obj;
lean_object* v_vals_2293_ = stack[3].m_obj;
lean_object* v_i_2295_ = stack[5].m_obj;
lean_object* v_entries_2296_ = stack[6].m_obj;
lean_object* v_res_2298_;
v_res_2298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_box(0), v_depth_2291_, v_keys_2292_, v_vals_2293_, lean_box(0), v_i_2295_, v_entries_2296_);
stack->m_obj
 = v_res_2298_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2299_, lean_object* v_depth_2300_, lean_object* v_keys_2301_, lean_object* v_vals_2302_, lean_object* v_heq_2303_, lean_object* v_i_2304_, lean_object* v_entries_2305_){
_start:
{
size_t v_depth_boxed_2306_; lean_object* v_res_2307_; 
v_depth_boxed_2306_ = lean_unbox_usize(v_depth_2300_);
lean_dec(v_depth_2300_);
v_res_2307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2299_, v_depth_boxed_2306_, v_keys_2301_, v_vals_2302_, v_heq_2303_, v_i_2304_, v_entries_2305_);
lean_dec_ref(v_vals_2302_);
lean_dec_ref(v_keys_2301_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23(lean_object* v_00_u03b2_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(v_x_2309_, v_x_2310_, v_x_2311_, v_x_2312_);
return v___x_2313_;
}
}
lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2314_, lean_object* v_maxArgs_x3f_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2314_, v_maxArgs_x3f_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT void l_Lean_Meta_getFunInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_2314_ = stack[0].m_obj;
lean_object* v_maxArgs_x3f_2315_ = stack[1].m_obj;
lean_object* v_a_2316_ = stack[2].m_obj;
lean_object* v_a_2317_ = stack[3].m_obj;
lean_object* v_a_2318_ = stack[4].m_obj;
lean_object* v_a_2319_ = stack[5].m_obj;
lean_object* v_res_2322_;
v_res_2322_ = l_Lean_Meta_getFunInfo(v_fn_2314_, v_maxArgs_x3f_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
stack->m_obj
 = v_res_2322_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2323_, lean_object* v_maxArgs_x3f_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Meta_getFunInfo(v_fn_2323_, v_maxArgs_x3f_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
return v_res_2330_;
}
}
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2331_, lean_object* v_nargs_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_nargs_2332_);
v___x_2339_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2331_, v___x_2338_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
return v___x_2339_;
}
}
LEAN_EXPORT void l_Lean_Meta_getFunInfoNArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_2331_ = stack[0].m_obj;
lean_object* v_nargs_2332_ = stack[1].m_obj;
lean_object* v_a_2333_ = stack[2].m_obj;
lean_object* v_a_2334_ = stack[3].m_obj;
lean_object* v_a_2335_ = stack[4].m_obj;
lean_object* v_a_2336_ = stack[5].m_obj;
lean_object* v_res_2340_;
v_res_2340_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2331_, v_nargs_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
stack->m_obj
 = v_res_2340_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2341_, lean_object* v_nargs_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2341_, v_nargs_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2349_){
_start:
{
lean_object* v_paramInfo_2350_; lean_object* v___x_2351_; 
v_paramInfo_2350_ = lean_ctor_get(v_info_2349_, 0);
v___x_2351_ = lean_array_get_size(v_paramInfo_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Meta_FunInfo_getArity(v_info_2352_);
lean_dec_ref(v_info_2352_);
return v_res_2353_;
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
