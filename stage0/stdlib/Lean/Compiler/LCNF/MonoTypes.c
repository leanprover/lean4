// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: public import Lean.Compiler.LCNF.Util public import Lean.Compiler.LCNF.BaseTypes public import Lean.Compiler.LCNF.Irrelevant
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MonoTypes"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 163, 188, 36, 234, 230, 12, 164)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(15, 104, 138, 221, 40, 128, 66, 209)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 193, 97, 55, 202, 162, 3, 38)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 79, 120, 160, 44, 67, 75, 103)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 5, 59, 84, 4, 22, 180, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "trivialStructureInfoExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 26, 11, 215, 188, 118, 90, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_getParamTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_getParamTypes___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getParamTypes___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_toMonoType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_toMonoType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toMonoType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.toMonoType.visitApp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.MonoTypes"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcAny"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "monoTypeExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 30, 14, 157, 163, 232, 91, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "` was not compiled; `compileDecls` must run on inductive types first"};
static const lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_k_3_ = lean_ctor_get(v_x_2_, 1);
v_v_4_ = lean_ctor_get(v_x_2_, 2);
v_l_5_ = lean_ctor_get(v_x_2_, 3);
v_r_6_ = lean_ctor_get(v_x_2_, 4);
v___x_7_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v_init_1_, v_l_5_);
lean_inc(v_v_4_);
lean_inc(v_k_3_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_k_3_);
lean_ctor_set(v___x_8_, 1, v_v_4_);
v___x_9_ = lean_array_push(v___x_7_, v___x_8_);
v_init_1_ = v___x_9_;
v_x_2_ = v_r_6_;
goto _start;
}
else
{
return v_init_1_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v_init_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(lean_object* v_env_14_, lean_object* v_as_15_, size_t v_i_16_, size_t v_stop_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___y_20_; uint8_t v___x_24_; 
v___x_24_ = lean_usize_dec_eq(v_i_16_, v_stop_17_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v_fst_26_; uint8_t v___x_27_; 
v___x_25_ = lean_array_uget_borrowed(v_as_15_, v_i_16_);
v_fst_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_fst_26_);
lean_inc_ref(v_env_14_);
v___x_27_ = l_Lean_Environment_contains(v_env_14_, v_fst_26_, v___x_24_);
if (v___x_27_ == 0)
{
v___y_20_ = v_b_18_;
goto v___jp_19_;
}
else
{
lean_object* v___x_28_; 
lean_inc(v___x_25_);
v___x_28_ = lean_array_push(v_b_18_, v___x_25_);
v___y_20_ = v___x_28_;
goto v___jp_19_;
}
}
else
{
lean_dec_ref(v_env_14_);
return v_b_18_;
}
v___jp_19_:
{
size_t v___x_21_; size_t v___x_22_; 
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_add(v_i_16_, v___x_21_);
v_i_16_ = v___x_22_;
v_b_18_ = v___y_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_29_, lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_stop_32_, lean_object* v_b_33_){
_start:
{
size_t v_i_boxed_34_; size_t v_stop_boxed_35_; lean_object* v_res_36_; 
v_i_boxed_34_ = lean_unbox_usize(v_i_31_);
lean_dec(v_i_31_);
v_stop_boxed_35_ = lean_unbox_usize(v_stop_32_);
lean_dec(v_stop_32_);
v_res_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(v_env_29_, v_as_30_, v_i_boxed_34_, v_stop_boxed_35_, v_b_33_);
lean_dec_ref(v_as_30_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(lean_object* v_env_37_, lean_object* v_as_38_, size_t v_i_39_, size_t v_stop_40_, lean_object* v_b_41_){
_start:
{
lean_object* v___y_43_; uint8_t v___x_47_; 
v___x_47_ = lean_usize_dec_eq(v_i_39_, v_stop_40_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v_fst_49_; uint8_t v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_48_ = lean_array_uget_borrowed(v_as_38_, v_i_39_);
v_fst_49_ = lean_ctor_get(v___x_48_, 0);
v___x_50_ = 1;
lean_inc_ref(v_env_37_);
v___x_51_ = l_Lean_Environment_setExporting(v_env_37_, v___x_50_);
lean_inc(v_fst_49_);
v___x_52_ = l_Lean_Environment_contains(v___x_51_, v_fst_49_, v___x_50_);
if (v___x_52_ == 0)
{
v___y_43_ = v_b_41_;
goto v___jp_42_;
}
else
{
lean_object* v___x_53_; 
lean_inc(v___x_48_);
v___x_53_ = lean_array_push(v_b_41_, v___x_48_);
v___y_43_ = v___x_53_;
goto v___jp_42_;
}
}
else
{
lean_dec_ref(v_env_37_);
return v_b_41_;
}
v___jp_42_:
{
size_t v___x_44_; size_t v___x_45_; 
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_add(v_i_39_, v___x_44_);
v_i_39_ = v___x_45_;
v_b_41_ = v___y_43_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_54_, lean_object* v_as_55_, lean_object* v_i_56_, lean_object* v_stop_57_, lean_object* v_b_58_){
_start:
{
size_t v_i_boxed_59_; size_t v_stop_boxed_60_; lean_object* v_res_61_; 
v_i_boxed_59_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_stop_boxed_60_ = lean_unbox_usize(v_stop_57_);
lean_dec(v_stop_57_);
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(v_env_54_, v_as_55_, v_i_boxed_59_, v_stop_boxed_60_, v_b_58_);
lean_dec_ref(v_as_55_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(lean_object* v___x_62_, lean_object* v_env_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_81_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v___x_81_, v_s_64_);
v___x_83_ = lean_array_get_size(v___x_82_);
v___x_84_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_85_ = lean_nat_dec_lt(v___x_62_, v___x_83_);
if (v___x_85_ == 0)
{
lean_dec_ref(v___x_82_);
v___y_66_ = v___x_84_;
goto v___jp_65_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_le(v___x_83_, v___x_83_);
if (v___x_86_ == 0)
{
if (v___x_85_ == 0)
{
lean_dec_ref(v___x_82_);
v___y_66_ = v___x_84_;
goto v___jp_65_;
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_83_);
lean_inc_ref(v_env_63_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(v_env_63_, v___x_82_, v___x_87_, v___x_88_, v___x_84_);
lean_dec_ref(v___x_82_);
v___y_66_ = v___x_89_;
goto v___jp_65_;
}
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_83_);
lean_inc_ref(v_env_63_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(v_env_63_, v___x_82_, v___x_90_, v___x_91_, v___x_84_);
lean_dec_ref(v___x_82_);
v___y_66_ = v___x_92_;
goto v___jp_65_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_array_get_size(v___y_66_);
v___x_68_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_69_ = lean_nat_dec_lt(v___x_62_, v___x_67_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v_env_63_);
lean_inc_ref(v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___y_66_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_le(v___x_67_, v___x_67_);
if (v___x_71_ == 0)
{
if (v___x_69_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_env_63_);
lean_inc_ref(v___x_68_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_68_);
lean_ctor_set(v___x_72_, 1, v___x_68_);
lean_ctor_set(v___x_72_, 2, v___y_66_);
return v___x_72_;
}
else
{
size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((size_t)0ULL);
v___x_74_ = lean_usize_of_nat(v___x_67_);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(v_env_63_, v___y_66_, v___x_73_, v___x_74_, v___x_68_);
lean_inc_ref(v___x_75_);
v___x_76_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
lean_ctor_set(v___x_76_, 2, v___y_66_);
return v___x_76_;
}
}
else
{
size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_67_);
v___x_79_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(v_env_63_, v___y_66_, v___x_77_, v___x_78_, v___x_68_);
lean_inc_ref(v___x_79_);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
lean_ctor_set(v___x_80_, 2, v___y_66_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v___x_93_, lean_object* v_env_94_, lean_object* v_s_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(v___x_93_, v_env_94_, v_s_95_);
lean_dec(v_s_95_);
lean_dec(v___x_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; 
v___f_136_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_137_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_138_ = lean_box(0);
v___x_139_ = 0;
v___x_140_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_137_, v___x_138_, v___x_139_, v___f_136_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(lean_object* v_init_143_, lean_object* v_t_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v_init_143_, v_t_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_146_, lean_object* v_t_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(v_init_146_, v_t_147_);
lean_dec(v_t_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(lean_object* v_type_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
lean_inc_ref(v_type_149_);
v___x_155_ = l_Lean_Meta_isProp(v_type_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; uint8_t v___x_157_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v___x_157_ = lean_unbox(v_a_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec_ref_known(v___x_155_, 1);
v___x_158_ = l_Lean_Meta_isTypeFormerType(v_type_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_158_;
}
else
{
lean_dec_ref(v_type_149_);
return v___x_155_;
}
}
else
{
lean_dec_ref(v_type_149_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed(lean_object* v_type_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(v_type_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object* v_declName_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0));
v___x_172_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_173_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_172_, v___f_171_, v_declName_167_, v_a_168_, v_a_169_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___boxed(lean_object* v_declName_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_declName_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* v_declName_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_184_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_183_, v_declName_179_, v_a_180_, v_a_181_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(lean_object* v_declName_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(lean_object* v_type_190_, lean_object* v_r_191_){
_start:
{
if (lean_obj_tag(v_type_190_) == 7)
{
lean_object* v_binderType_192_; lean_object* v_body_193_; lean_object* v___x_194_; 
v_binderType_192_ = lean_ctor_get(v_type_190_, 1);
lean_inc_ref(v_binderType_192_);
v_body_193_ = lean_ctor_get(v_type_190_, 2);
lean_inc_ref(v_body_193_);
lean_dec_ref_known(v_type_190_, 3);
v___x_194_ = lean_array_push(v_r_191_, v_binderType_192_);
v_type_190_ = v_body_193_;
v_r_191_ = v___x_194_;
goto _start;
}
else
{
lean_dec_ref(v_type_190_);
return v_r_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* v_type_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_200_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(v_type_198_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___f_206_; lean_object* v___x_2863__overap_207_; lean_object* v___x_208_; 
v___f_206_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0));
v___x_2863__overap_207_ = lean_panic_fn_borrowed(v___f_206_, v_msg_202_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
v___x_208_ = lean_apply_3(v___x_2863__overap_207_, v___y_203_, v___y_204_, lean_box(0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v_msg_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v_dummy_215_; 
v___x_214_ = lean_box(0);
v_dummy_215_ = l_Lean_Expr_sort___override(v___x_214_);
return v_dummy_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object* v_type_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_type_221_; 
v_type_221_ = l_Lean_Expr_headBeta(v_type_217_);
switch(lean_obj_tag(v_type_221_))
{
case 4:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_223_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_type_221_, v___x_222_, v_a_218_, v_a_219_);
return v___x_223_;
}
case 5:
{
lean_object* v_dummy_224_; lean_object* v_nargs_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_dummy_224_ = lean_obj_once(&l_Lean_Compiler_LCNF_toMonoType___closed__0, &l_Lean_Compiler_LCNF_toMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_toMonoType___closed__0);
v_nargs_225_ = l_Lean_Expr_getAppNumArgs(v_type_221_);
lean_inc(v_nargs_225_);
v___x_226_ = lean_mk_array(v_nargs_225_, v_dummy_224_);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_sub(v_nargs_225_, v___x_227_);
lean_dec(v_nargs_225_);
v___x_229_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_type_221_, v___x_226_, v___x_228_, v_a_218_, v_a_219_);
return v___x_229_;
}
case 7:
{
lean_object* v_binderName_230_; lean_object* v_binderType_231_; lean_object* v_body_232_; uint8_t v_binderInfo_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_binderName_230_ = lean_ctor_get(v_type_221_, 0);
lean_inc(v_binderName_230_);
v_binderType_231_ = lean_ctor_get(v_type_221_, 1);
lean_inc_ref(v_binderType_231_);
v_body_232_ = lean_ctor_get(v_type_221_, 2);
lean_inc_ref(v_body_232_);
v_binderInfo_233_ = lean_ctor_get_uint8(v_type_221_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_221_, 3);
v___x_234_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_235_ = lean_expr_instantiate1(v_body_232_, v___x_234_);
lean_dec_ref(v_body_232_);
v___x_236_ = l_Lean_Compiler_LCNF_toMonoType(v___x_235_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_263_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_263_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_263_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_263_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; lean_object* v___y_243_; 
if (lean_obj_tag(v_a_237_) == 4)
{
lean_object* v_declName_254_; 
v_declName_254_ = lean_ctor_get(v_a_237_, 0);
if (lean_obj_tag(v_declName_254_) == 1)
{
lean_object* v_pre_255_; 
v_pre_255_ = lean_ctor_get(v_declName_254_, 0);
if (lean_obj_tag(v_pre_255_) == 0)
{
lean_object* v_str_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_str_256_ = lean_ctor_get(v_declName_254_, 1);
v___x_257_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_258_ = lean_string_dec_eq(v_str_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_del_object(v___x_239_);
v___y_242_ = v_a_218_;
v___y_243_ = v_a_219_;
goto v___jp_241_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec_ref_known(v_a_237_, 2);
lean_dec_ref(v_binderType_231_);
lean_dec(v_binderName_230_);
v___x_259_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_259_);
v___x_261_ = v___x_239_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_del_object(v___x_239_);
v___y_242_ = v_a_218_;
v___y_243_ = v_a_219_;
goto v___jp_241_;
}
}
else
{
lean_del_object(v___x_239_);
v___y_242_ = v_a_218_;
v___y_243_ = v_a_219_;
goto v___jp_241_;
}
}
else
{
lean_del_object(v___x_239_);
v___y_242_ = v_a_218_;
v___y_243_ = v_a_219_;
goto v___jp_241_;
}
v___jp_241_:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_231_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = l_Lean_Expr_forallE___override(v_binderName_230_, v_a_245_, v_a_237_, v_binderInfo_233_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_dec(v_a_237_);
lean_dec(v_binderName_230_);
return v___x_244_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_231_);
lean_dec(v_binderName_230_);
return v___x_236_;
}
}
case 3:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref_known(v_type_221_, 1);
v___x_264_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
case 10:
{
lean_object* v_data_266_; lean_object* v_expr_267_; lean_object* v___x_268_; 
v_data_266_ = lean_ctor_get(v_type_221_, 0);
lean_inc(v_data_266_);
v_expr_267_ = lean_ctor_get(v_type_221_, 1);
lean_inc_ref(v_expr_267_);
lean_dec_ref_known(v_type_221_, 2);
v___x_268_ = l_Lean_Compiler_LCNF_toMonoType(v_expr_267_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_Expr_mdata___override(v_data_266_, v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_dec(v_data_266_);
return v___x_268_;
}
}
default: 
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_type_221_);
v___x_278_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2));
v___x_284_ = lean_unsigned_to_nat(50u);
v___x_285_ = lean_unsigned_to_nat(81u);
v___x_286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1));
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0));
v___x_288_ = l_mkPanicMessageWithDecl(v___x_287_, v___x_286_, v___x_285_, v___x_284_, v___x_283_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t v___x_289_, lean_object* v_as_290_, size_t v_sz_291_, size_t v_i_292_, lean_object* v_b_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_a_298_; uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_292_, v_sz_291_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_b_293_);
return v___x_303_;
}
else
{
lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_354_; 
v_fst_304_ = lean_ctor_get(v_b_293_, 0);
v_snd_305_ = lean_ctor_get(v_b_293_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_b_293_);
if (v_isSharedCheck_354_ == 0)
{
v___x_307_ = v_b_293_;
v_isShared_308_ = v_isSharedCheck_354_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_snd_305_);
lean_inc(v_fst_304_);
lean_dec(v_b_293_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_354_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; 
lean_inc(v_snd_305_);
v___x_309_ = l_Lean_Expr_headBeta(v_snd_305_);
if (lean_obj_tag(v___x_309_) == 7)
{
lean_object* v_binderType_310_; lean_object* v_body_311_; lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v_result_315_; uint8_t v___y_333_; 
lean_dec(v_snd_305_);
v_binderType_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc_ref(v_binderType_310_);
v_body_311_ = lean_ctor_get(v___x_309_, 2);
lean_inc_ref(v_body_311_);
lean_dec_ref_known(v___x_309_, 3);
v_a_312_ = lean_array_uget_borrowed(v_as_290_, v_i_292_);
lean_inc(v_a_312_);
v___x_313_ = l_Lean_Expr_headBeta(v_a_312_);
switch(lean_obj_tag(v_binderType_310_))
{
case 4:
{
lean_object* v_declName_336_; 
v_declName_336_ = lean_ctor_get(v_binderType_310_, 0);
lean_inc(v_declName_336_);
lean_dec_ref_known(v_binderType_310_, 2);
if (lean_obj_tag(v_declName_336_) == 1)
{
lean_object* v_pre_337_; 
v_pre_337_ = lean_ctor_get(v_declName_336_, 0);
if (lean_obj_tag(v_pre_337_) == 0)
{
lean_object* v_str_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_str_338_ = lean_ctor_get(v_declName_336_, 1);
lean_inc_ref(v_str_338_);
lean_dec_ref_known(v_declName_336_, 2);
v___x_339_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_340_ = lean_string_dec_eq(v_str_338_, v___x_339_);
lean_dec_ref(v_str_338_);
if (v___x_340_ == 0)
{
v___y_333_ = v___x_289_;
goto v___jp_332_;
}
else
{
goto v___jp_320_;
}
}
else
{
lean_dec_ref_known(v_declName_336_, 2);
v___y_333_ = v___x_289_;
goto v___jp_332_;
}
}
else
{
lean_dec(v_declName_336_);
v___y_333_ = v___x_289_;
goto v___jp_332_;
}
}
case 3:
{
lean_dec_ref_known(v_binderType_310_, 1);
goto v___jp_320_;
}
default: 
{
lean_dec_ref(v_binderType_310_);
v___y_333_ = v___x_289_;
goto v___jp_332_;
}
}
v___jp_314_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_expr_instantiate1(v_body_311_, v___x_313_);
lean_dec_ref(v___x_313_);
lean_dec_ref(v_body_311_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_316_);
lean_ctor_set(v___x_307_, 0, v_result_315_);
v___x_318_ = v___x_307_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_result_315_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v_a_298_ = v___x_318_;
goto v___jp_297_;
}
}
v___jp_320_:
{
lean_object* v___x_321_; 
lean_inc_ref(v___x_313_);
v___x_321_ = l_Lean_Compiler_LCNF_toMonoType(v___x_313_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_Lean_Expr_app___override(v_fst_304_, v_a_322_);
v_result_315_ = v___x_323_;
goto v___jp_314_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v___x_313_);
lean_dec_ref(v_body_311_);
lean_del_object(v___x_307_);
lean_dec(v_fst_304_);
v_a_324_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_321_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_335_ = l_Lean_Expr_app___override(v_fst_304_, v___x_334_);
v_result_315_ = v___x_335_;
goto v___jp_314_;
}
else
{
goto v___jp_320_;
}
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref(v___x_309_);
v___x_341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3);
v___x_342_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v___x_341_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_342_, 1);
if (v_isShared_308_ == 0)
{
v___x_344_ = v___x_307_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_fst_304_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_305_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
v_a_298_ = v___x_344_;
goto v___jp_297_;
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_del_object(v___x_307_);
lean_dec(v_snd_305_);
lean_dec(v_fst_304_);
v_a_346_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_342_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_342_);
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
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
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
}
v___jp_297_:
{
size_t v___x_299_; size_t v___x_300_; 
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_292_, v___x_299_);
v_i_292_ = v___x_300_;
v_b_293_ = v_a_298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* v_f_356_, lean_object* v_args_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
if (lean_obj_tag(v_f_356_) == 4)
{
lean_object* v_declName_361_; lean_object* v_us_362_; lean_object* v___x_363_; lean_object* v___y_365_; lean_object* v___y_366_; 
v_declName_361_ = lean_ctor_get(v_f_356_, 0);
lean_inc(v_declName_361_);
v_us_362_ = lean_ctor_get(v_f_356_, 1);
lean_inc(v_us_362_);
lean_dec_ref_known(v_f_356_, 2);
v___x_363_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_declName_361_) == 1)
{
lean_object* v_pre_426_; 
v_pre_426_ = lean_ctor_get(v_declName_361_, 0);
if (lean_obj_tag(v_pre_426_) == 0)
{
lean_object* v_str_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_str_427_ = lean_ctor_get(v_declName_361_, 1);
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_429_ = lean_string_dec_eq(v_str_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0));
v___x_431_ = lean_string_dec_eq(v_str_427_, v___x_430_);
if (v___x_431_ == 0)
{
v___y_365_ = v_a_358_;
v___y_366_ = v_a_359_;
goto v___jp_364_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref_known(v_declName_361_, 2);
lean_dec(v_us_362_);
lean_dec_ref(v_args_357_);
v___x_432_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref_known(v_declName_361_, 2);
lean_dec(v_us_362_);
lean_dec_ref(v_args_357_);
v___x_434_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
else
{
v___y_365_ = v_a_358_;
v___y_366_ = v_a_359_;
goto v___jp_364_;
}
}
else
{
v___y_365_ = v_a_358_;
v___y_366_ = v_a_359_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_367_; 
lean_inc(v_declName_361_);
v___x_367_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_361_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
if (lean_obj_tag(v_a_368_) == 1)
{
lean_object* v_val_369_; lean_object* v_ctorName_370_; lean_object* v_numParams_371_; lean_object* v_fieldIdx_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_us_362_);
lean_dec(v_declName_361_);
v_val_369_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_a_368_, 1);
v_ctorName_370_ = lean_ctor_get(v_val_369_, 0);
lean_inc(v_ctorName_370_);
v_numParams_371_ = lean_ctor_get(v_val_369_, 1);
lean_inc(v_numParams_371_);
v_fieldIdx_372_ = lean_ctor_get(v_val_369_, 2);
lean_inc(v_fieldIdx_372_);
lean_dec(v_val_369_);
v___x_373_ = lean_box(0);
v___x_374_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_370_, v___x_373_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l_Array_toSubarray___redArg(v_args_357_, v___x_376_, v_numParams_371_);
v___x_378_ = l_Subarray_copy___redArg(v___x_377_);
v___x_379_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_375_, v___x_378_, v___y_365_, v___y_366_);
lean_dec_ref(v___x_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_380_);
v___x_382_ = lean_array_get(v___x_363_, v___x_381_, v_fieldIdx_372_);
lean_dec(v_fieldIdx_372_);
lean_dec_ref(v___x_381_);
v___x_383_ = l_Lean_Compiler_LCNF_toMonoType(v___x_382_, v___y_365_, v___y_366_);
return v___x_383_;
}
else
{
lean_dec(v_fieldIdx_372_);
return v___x_379_;
}
}
else
{
lean_dec(v_fieldIdx_372_);
lean_dec(v_numParams_371_);
lean_dec_ref(v_args_357_);
return v___x_374_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_a_368_);
v___x_384_ = lean_box(0);
lean_inc(v_declName_361_);
v___x_385_ = l_Lean_mkConst(v_declName_361_, v___x_384_);
v___x_386_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_361_, v_us_362_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_417_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_417_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_417_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_417_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_Expr_isErased(v_a_387_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; size_t v_sz_393_; size_t v___x_394_; lean_object* v___x_395_; 
lean_del_object(v___x_389_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_385_);
lean_ctor_set(v___x_392_, 1, v_a_387_);
v_sz_393_ = lean_array_size(v_args_357_);
v___x_394_ = ((size_t)0ULL);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_391_, v_args_357_, v_sz_393_, v___x_394_, v___x_392_, v___y_365_, v___y_366_);
lean_dec_ref(v_args_357_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_fst_400_; lean_object* v___x_402_; 
v_fst_400_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_fst_400_);
lean_dec(v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_fst_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_fst_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_395_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec(v_a_387_);
lean_dec_ref(v___x_385_);
lean_dec_ref(v_args_357_);
v___x_413_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_413_);
v___x_415_ = v___x_389_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_dec_ref(v___x_385_);
lean_dec_ref(v_args_357_);
return v___x_386_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_us_362_);
lean_dec(v_declName_361_);
lean_dec_ref(v_args_357_);
v_a_418_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_367_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_367_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_args_357_);
lean_dec_ref(v_f_356_);
v___x_436_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
if (lean_obj_tag(v_x_438_) == 5)
{
lean_object* v_fn_444_; lean_object* v_arg_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_fn_444_ = lean_ctor_get(v_x_438_, 0);
lean_inc_ref(v_fn_444_);
v_arg_445_ = lean_ctor_get(v_x_438_, 1);
lean_inc_ref(v_arg_445_);
lean_dec_ref_known(v_x_438_, 2);
v___x_446_ = lean_array_set(v_x_439_, v_x_440_, v_arg_445_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v_x_440_, v___x_447_);
lean_dec(v_x_440_);
v_x_438_ = v_fn_444_;
v_x_439_ = v___x_446_;
v_x_440_ = v___x_448_;
goto _start;
}
else
{
lean_object* v___x_450_; 
lean_dec(v_x_440_);
v___x_450_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_x_438_, v_x_439_, v___y_441_, v___y_442_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_x_451_, v_x_452_, v_x_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object* v_type_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Compiler_LCNF_toMonoType(v_type_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object* v___x_463_, lean_object* v_as_464_, lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_3339__boxed_471_; size_t v_sz_boxed_472_; size_t v_i_boxed_473_; lean_object* v_res_474_; 
v___x_3339__boxed_471_ = lean_unbox(v___x_463_);
v_sz_boxed_472_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_473_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_3339__boxed_471_, v_as_464_, v_sz_boxed_472_, v_i_boxed_473_, v_b_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_as_464_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(lean_object* v_f_475_, lean_object* v_args_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_f_475_, v_args_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(lean_object* v_env_481_, lean_object* v_as_482_, size_t v_i_483_, size_t v_stop_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___y_487_; uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_eq(v_i_483_, v_stop_484_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v_fst_493_; uint8_t v___x_494_; 
v___x_492_ = lean_array_uget_borrowed(v_as_482_, v_i_483_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_fst_493_);
lean_inc_ref(v_env_481_);
v___x_494_ = l_Lean_Environment_contains(v_env_481_, v_fst_493_, v___x_491_);
if (v___x_494_ == 0)
{
v___y_487_ = v_b_485_;
goto v___jp_486_;
}
else
{
lean_object* v___x_495_; 
lean_inc(v___x_492_);
v___x_495_ = lean_array_push(v_b_485_, v___x_492_);
v___y_487_ = v___x_495_;
goto v___jp_486_;
}
}
else
{
lean_dec_ref(v_env_481_);
return v_b_485_;
}
v___jp_486_:
{
size_t v___x_488_; size_t v___x_489_; 
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_483_, v___x_488_);
v_i_483_ = v___x_489_;
v_b_485_ = v___y_487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_496_, lean_object* v_as_497_, lean_object* v_i_498_, lean_object* v_stop_499_, lean_object* v_b_500_){
_start:
{
size_t v_i_boxed_501_; size_t v_stop_boxed_502_; lean_object* v_res_503_; 
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_stop_boxed_502_ = lean_unbox_usize(v_stop_499_);
lean_dec(v_stop_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(v_env_496_, v_as_497_, v_i_boxed_501_, v_stop_boxed_502_, v_b_500_);
lean_dec_ref(v_as_497_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_k_506_; lean_object* v_v_507_; lean_object* v_l_508_; lean_object* v_r_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_k_506_ = lean_ctor_get(v_x_505_, 1);
v_v_507_ = lean_ctor_get(v_x_505_, 2);
v_l_508_ = lean_ctor_get(v_x_505_, 3);
v_r_509_ = lean_ctor_get(v_x_505_, 4);
v___x_510_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_504_, v_l_508_);
lean_inc(v_v_507_);
lean_inc(v_k_506_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_k_506_);
lean_ctor_set(v___x_511_, 1, v_v_507_);
v___x_512_ = lean_array_push(v___x_510_, v___x_511_);
v_init_504_ = v___x_512_;
v_x_505_ = v_r_509_;
goto _start;
}
else
{
return v_init_504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_514_, lean_object* v_x_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_514_, v_x_515_);
lean_dec(v_x_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(lean_object* v_env_517_, lean_object* v_as_518_, size_t v_i_519_, size_t v_stop_520_, lean_object* v_b_521_){
_start:
{
lean_object* v___y_523_; uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_eq(v_i_519_, v_stop_520_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v_fst_529_; uint8_t v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_528_ = lean_array_uget_borrowed(v_as_518_, v_i_519_);
v_fst_529_ = lean_ctor_get(v___x_528_, 0);
v___x_530_ = 1;
lean_inc_ref(v_env_517_);
v___x_531_ = l_Lean_Environment_setExporting(v_env_517_, v___x_530_);
lean_inc(v_fst_529_);
v___x_532_ = l_Lean_Environment_contains(v___x_531_, v_fst_529_, v___x_530_);
if (v___x_532_ == 0)
{
v___y_523_ = v_b_521_;
goto v___jp_522_;
}
else
{
lean_object* v___x_533_; 
lean_inc(v___x_528_);
v___x_533_ = lean_array_push(v_b_521_, v___x_528_);
v___y_523_ = v___x_533_;
goto v___jp_522_;
}
}
else
{
lean_dec_ref(v_env_517_);
return v_b_521_;
}
v___jp_522_:
{
size_t v___x_524_; size_t v___x_525_; 
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_519_, v___x_524_);
v_i_519_ = v___x_525_;
v_b_521_ = v___y_523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_534_, lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_, lean_object* v_b_538_){
_start:
{
size_t v_i_boxed_539_; size_t v_stop_boxed_540_; lean_object* v_res_541_; 
v_i_boxed_539_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_540_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_534_, v_as_535_, v_i_boxed_539_, v_stop_boxed_540_, v_b_538_);
lean_dec_ref(v_as_535_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(lean_object* v_env_546_, lean_object* v_s_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___y_550_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_566_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v___x_565_, v_s_547_);
v___x_567_ = lean_array_get_size(v___x_566_);
v___x_568_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_569_ = lean_nat_dec_lt(v___x_548_, v___x_567_);
if (v___x_569_ == 0)
{
lean_dec_ref(v___x_566_);
v___y_550_ = v___x_568_;
goto v___jp_549_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_le(v___x_567_, v___x_567_);
if (v___x_570_ == 0)
{
if (v___x_569_ == 0)
{
lean_dec_ref(v___x_566_);
v___y_550_ = v___x_568_;
goto v___jp_549_;
}
else
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = ((size_t)0ULL);
v___x_572_ = lean_usize_of_nat(v___x_567_);
lean_inc_ref(v_env_546_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(v_env_546_, v___x_566_, v___x_571_, v___x_572_, v___x_568_);
lean_dec_ref(v___x_566_);
v___y_550_ = v___x_573_;
goto v___jp_549_;
}
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((size_t)0ULL);
v___x_575_ = lean_usize_of_nat(v___x_567_);
lean_inc_ref(v_env_546_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(v_env_546_, v___x_566_, v___x_574_, v___x_575_, v___x_568_);
lean_dec_ref(v___x_566_);
v___y_550_ = v___x_576_;
goto v___jp_549_;
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_array_get_size(v___y_550_);
v___x_552_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_553_ = lean_nat_dec_lt(v___x_548_, v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec_ref(v_env_546_);
v___x_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___y_550_);
return v___x_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_le(v___x_551_, v___x_551_);
if (v___x_555_ == 0)
{
if (v___x_553_ == 0)
{
lean_object* v___x_556_; 
lean_dec_ref(v_env_546_);
v___x_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_556_, 0, v___x_552_);
lean_ctor_set(v___x_556_, 1, v___x_552_);
lean_ctor_set(v___x_556_, 2, v___y_550_);
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_551_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_546_, v___y_550_, v___x_557_, v___x_558_, v___x_552_);
lean_inc_ref(v___x_559_);
v___x_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
lean_ctor_set(v___x_560_, 2, v___y_550_);
return v___x_560_;
}
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_551_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_546_, v___y_550_, v___x_561_, v___x_562_, v___x_552_);
lean_inc_ref(v___x_563_);
v___x_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
lean_ctor_set(v___x_564_, 2, v___y_550_);
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_env_577_, lean_object* v_s_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(v_env_577_, v_s_578_);
lean_dec(v_s_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v___f_588_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_589_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_590_ = lean_box(0);
v___x_591_ = 0;
v___x_592_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_589_, v___x_590_, v___x_591_, v___f_588_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(lean_object* v_init_595_, lean_object* v_t_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_595_, v_t_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_598_, lean_object* v_t_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(v_init_598_, v_t_599_);
lean_dec(v_t_599_);
return v_res_600_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object* v_declName_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v___x_613_; lean_object* v_toEnvExtension_614_; lean_object* v_asyncMode_615_; uint8_t v___x_616_; lean_object* v___x_617_; 
v___x_610_ = l_Lean_instInhabitedExpr;
v___x_611_ = lean_st_ref_get(v_a_608_);
v_env_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc_ref(v_env_612_);
lean_dec(v___x_611_);
v___x_613_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_614_ = lean_ctor_get(v___x_613_, 0);
v_asyncMode_615_ = lean_ctor_get(v_toEnvExtension_614_, 2);
v___x_616_ = 0;
lean_inc(v_declName_606_);
v___x_617_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_610_, v___x_613_, v_env_612_, v_declName_606_, v_asyncMode_615_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = 0;
v___x_619_ = lean_box(0);
lean_inc(v_declName_606_);
v___x_620_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_606_, v___x_619_, v_a_607_, v_a_608_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_Lean_Compiler_LCNF_toMonoType(v_a_621_, v_a_607_, v_a_608_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_652_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_652_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_652_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_652_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v_env_628_; lean_object* v_nextMacroScope_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_traceState_632_; lean_object* v_recordedDeps_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_650_; 
v___x_627_ = lean_st_ref_take(v_a_608_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
v_nextMacroScope_629_ = lean_ctor_get(v___x_627_, 1);
v_ngen_630_ = lean_ctor_get(v___x_627_, 2);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_627_, 3);
v_traceState_632_ = lean_ctor_get(v___x_627_, 4);
v_recordedDeps_633_ = lean_ctor_get(v___x_627_, 6);
v_messages_634_ = lean_ctor_get(v___x_627_, 7);
v_infoState_635_ = lean_ctor_get(v___x_627_, 8);
v_snapshotTasks_636_ = lean_ctor_get(v___x_627_, 9);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_627_, 5);
lean_dec(v_unused_651_);
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_635_);
lean_inc(v_messages_634_);
lean_inc(v_recordedDeps_633_);
lean_inc(v_traceState_632_);
lean_inc(v_auxDeclNGen_631_);
lean_inc(v_ngen_630_);
lean_inc(v_nextMacroScope_629_);
lean_inc(v_env_628_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_640_ = lean_box(0);
v___x_641_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_613_, v_env_628_, v_declName_606_, v_a_623_, v___x_618_);
v___x_642_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 5, v___x_642_);
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_644_ = v___x_638_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_nextMacroScope_629_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_ngen_630_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_auxDeclNGen_631_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_traceState_632_);
lean_ctor_set(v_reuseFailAlloc_649_, 5, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_649_, 6, v_recordedDeps_633_);
lean_ctor_set(v_reuseFailAlloc_649_, 7, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_649_, 8, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_649_, 9, v_snapshotTasks_636_);
v___x_644_ = v_reuseFailAlloc_649_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_st_ref_put(v_a_608_, v___x_644_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_640_);
v___x_647_ = v___x_625_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_640_);
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
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_declName_606_);
v_a_653_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_622_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_622_);
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
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_declName_606_);
v_a_661_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_620_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_620_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_declName_606_);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_677_);
v___x_670_ = v___x_617_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_617_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 0);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___boxed(lean_object* v_declName_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_declName_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0(lean_object* v___x_683_, lean_object* v_declName_684_, lean_object* v_a_685_, lean_object* v_ps_686_){
_start:
{
lean_object* v_importedEntries_687_; lean_object* v_state_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v_importedEntries_687_ = lean_ctor_get(v_ps_686_, 0);
v_state_688_ = lean_ctor_get(v_ps_686_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_ps_686_);
if (v_isSharedCheck_698_ == 0)
{
v___x_690_ = v_ps_686_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_state_688_);
lean_inc(v_importedEntries_687_);
lean_dec(v_ps_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_addEntryFn_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_addEntryFn_692_ = lean_ctor_get(v___x_683_, 3);
lean_inc(v_addEntryFn_692_);
lean_dec_ref(v___x_683_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_declName_684_);
lean_ctor_set(v___x_693_, 1, v_a_685_);
v___x_694_ = lean_apply_2(v_addEntryFn_692_, v_state_688_, v___x_693_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_importedEntries_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_702_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
lean_ctor_set(v___x_704_, 3, v___x_703_);
lean_ctor_set(v___x_704_, 4, v___x_702_);
lean_ctor_set(v___x_704_, 5, v___x_702_);
lean_ctor_set(v___x_704_, 6, v___x_702_);
lean_ctor_set(v___x_704_, 7, v___x_702_);
lean_ctor_set(v___x_704_, 8, v___x_702_);
lean_ctor_set(v___x_704_, 9, v___x_702_);
lean_ctor_set(v___x_704_, 10, v___x_702_);
lean_ctor_set(v___x_704_, 11, v___x_701_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(32u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_708_ = ((size_t)5ULL);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_unsigned_to_nat(32u);
v___x_711_ = lean_mk_empty_array_with_capacity(v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2);
v___x_713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
lean_ctor_set(v___x_713_, 2, v___x_709_);
lean_ctor_set(v___x_713_, 3, v___x_709_);
lean_ctor_set_usize(v___x_713_, 4, v___x_708_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = lean_box(1);
v___x_715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3);
v___x_716_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_toCold_723_; lean_object* v_env_724_; lean_object* v_options_725_; uint8_t v___x_726_; lean_object* v_env_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_722_ = lean_st_ref_get(v___y_720_);
v_toCold_723_ = lean_ctor_get(v___y_719_, 0);
v_env_724_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_724_);
lean_dec(v___x_722_);
v_options_725_ = lean_ctor_get(v_toCold_723_, 2);
v___x_726_ = 0;
v_env_727_ = l_Lean_Environment_setRecordingDeps(v_env_724_, v___x_726_);
v___x_728_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1);
v___x_729_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_725_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_env_727_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_729_);
lean_ctor_set(v___x_730_, 3, v_options_725_);
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_msgData_718_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___boxed(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msgData_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_ref_742_; lean_object* v___x_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_ref_742_ = lean_ctor_get(v___y_739_, 2);
v___x_743_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msg_738_, v___y_739_, v___y_740_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc(v_ref_742_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_ref_742_);
lean_ctor_set(v___x_748_, 1, v_a_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_757_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* v_declName_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_nextMacroScope_769_; lean_object* v_ngen_770_; lean_object* v_auxDeclNGen_771_; lean_object* v_traceState_772_; lean_object* v_recordedDeps_773_; lean_object* v_messages_774_; lean_object* v_infoState_775_; lean_object* v_snapshotTasks_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_env_814_; lean_object* v___x_815_; lean_object* v_toEnvExtension_816_; lean_object* v_asyncMode_817_; uint8_t v___x_818_; lean_object* v___x_819_; 
v___x_812_ = l_Lean_instInhabitedExpr;
v___x_813_ = lean_st_ref_get(v_a_766_);
v_env_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref(v_env_814_);
lean_dec(v___x_813_);
v___x_815_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_816_ = lean_ctor_get(v___x_815_, 0);
v_asyncMode_817_ = lean_ctor_get(v_toEnvExtension_816_, 2);
v___x_818_ = 0;
lean_inc(v_declName_764_);
v___x_819_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_812_, v___x_815_, v_env_814_, v_declName_764_, v_asyncMode_817_, v___x_818_);
if (lean_obj_tag(v___x_819_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_declName_764_);
v_val_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_val_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v___x_828_; lean_object* v_env_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
lean_dec(v___x_819_);
v___x_828_ = lean_st_ref_get(v_a_766_);
v_env_844_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_844_);
lean_dec(v___x_828_);
v___x_845_ = 0;
lean_inc(v_declName_764_);
v___x_846_ = l_Lean_Environment_find_x3f(v_env_844_, v_declName_764_, v___x_845_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
switch(lean_obj_tag(v_val_847_))
{
case 5:
{
lean_dec_ref_known(v_val_847_, 1);
goto v___jp_829_;
}
case 6:
{
lean_dec_ref_known(v_val_847_, 1);
goto v___jp_829_;
}
default: 
{
lean_dec(v_val_847_);
v___y_785_ = v_a_765_;
v___y_786_ = v_a_766_;
goto v___jp_784_;
}
}
}
else
{
lean_dec(v___x_846_);
v___y_785_ = v_a_765_;
v___y_786_ = v_a_766_;
goto v___jp_784_;
}
v___jp_829_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v___x_830_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1);
v___x_831_ = l_Lean_MessageData_ofName(v_declName_764_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v___x_834_, v_a_765_, v_a_766_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
v___jp_768_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
v___x_781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_781_, 0, v___y_779_);
lean_ctor_set(v___x_781_, 1, v_nextMacroScope_769_);
lean_ctor_set(v___x_781_, 2, v_ngen_770_);
lean_ctor_set(v___x_781_, 3, v_auxDeclNGen_771_);
lean_ctor_set(v___x_781_, 4, v_traceState_772_);
lean_ctor_set(v___x_781_, 5, v___x_780_);
lean_ctor_set(v___x_781_, 6, v_recordedDeps_773_);
lean_ctor_set(v___x_781_, 7, v_messages_774_);
lean_ctor_set(v___x_781_, 8, v_infoState_775_);
lean_ctor_set(v___x_781_, 9, v_snapshotTasks_776_);
v___x_782_ = lean_st_ref_put(v___y_778_, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___y_777_);
return v___x_783_;
}
v___jp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box(0);
lean_inc(v_declName_764_);
v___x_788_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_764_, v___x_787_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = l_Lean_Compiler_LCNF_toMonoType(v_a_789_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; lean_object* v_env_793_; lean_object* v_nextMacroScope_794_; lean_object* v_ngen_795_; lean_object* v_auxDeclNGen_796_; lean_object* v_traceState_797_; lean_object* v_recordedDeps_798_; lean_object* v_messages_799_; lean_object* v_infoState_800_; lean_object* v_snapshotTasks_801_; lean_object* v___x_802_; lean_object* v_toEnvExtension_803_; lean_object* v_asyncMode_804_; uint8_t v_logWrites_805_; lean_object* v___f_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_n(v_a_791_, 2);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = lean_st_ref_take(v___y_786_);
v_env_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc_ref(v_env_793_);
v_nextMacroScope_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_nextMacroScope_794_);
v_ngen_795_ = lean_ctor_get(v___x_792_, 2);
lean_inc_ref(v_ngen_795_);
v_auxDeclNGen_796_ = lean_ctor_get(v___x_792_, 3);
lean_inc_ref(v_auxDeclNGen_796_);
v_traceState_797_ = lean_ctor_get(v___x_792_, 4);
lean_inc_ref(v_traceState_797_);
v_recordedDeps_798_ = lean_ctor_get(v___x_792_, 6);
lean_inc_ref(v_recordedDeps_798_);
v_messages_799_ = lean_ctor_get(v___x_792_, 7);
lean_inc_ref(v_messages_799_);
v_infoState_800_ = lean_ctor_get(v___x_792_, 8);
lean_inc_ref(v_infoState_800_);
v_snapshotTasks_801_ = lean_ctor_get(v___x_792_, 9);
lean_inc_ref(v_snapshotTasks_801_);
lean_dec(v___x_792_);
v___x_802_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_803_ = lean_ctor_get(v___x_802_, 0);
v_asyncMode_804_ = lean_ctor_get(v_toEnvExtension_803_, 2);
v_logWrites_805_ = lean_ctor_get_uint8(v_toEnvExtension_803_, sizeof(void*)*6);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0), 4, 3);
lean_closure_set(v___f_806_, 0, v___x_802_);
lean_closure_set(v___f_806_, 1, v_declName_764_);
lean_closure_set(v___f_806_, 2, v_a_791_);
v___x_807_ = lean_box(0);
v___x_808_ = 1;
if (v_logWrites_805_ == 0)
{
lean_object* v___x_809_; 
lean_inc_ref(v_toEnvExtension_803_);
v___x_809_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_803_, v_env_793_, v___f_806_, v_asyncMode_804_, v___x_807_, v___x_808_);
v_nextMacroScope_769_ = v_nextMacroScope_794_;
v_ngen_770_ = v_ngen_795_;
v_auxDeclNGen_771_ = v_auxDeclNGen_796_;
v_traceState_772_ = v_traceState_797_;
v_recordedDeps_773_ = v_recordedDeps_798_;
v_messages_774_ = v_messages_799_;
v_infoState_775_ = v_infoState_800_;
v_snapshotTasks_776_ = v_snapshotTasks_801_;
v___y_777_ = v_a_791_;
v___y_778_ = v___y_786_;
v___y_779_ = v___x_809_;
goto v___jp_768_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_inc_ref_n(v_toEnvExtension_803_, 2);
v___x_810_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_803_, v_env_793_);
lean_dec_ref(v_env_793_);
v___x_811_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_803_, v___x_810_, v___f_806_, v_asyncMode_804_, v___x_807_, v___x_808_);
v_nextMacroScope_769_ = v_nextMacroScope_794_;
v_ngen_770_ = v_ngen_795_;
v_auxDeclNGen_771_ = v_auxDeclNGen_796_;
v_traceState_772_ = v_traceState_797_;
v_recordedDeps_773_ = v_recordedDeps_798_;
v_messages_774_ = v_messages_799_;
v_infoState_775_ = v_infoState_800_;
v_snapshotTasks_776_ = v_snapshotTasks_801_;
v___y_777_ = v_a_791_;
v___y_778_ = v___y_786_;
v___y_779_ = v___x_811_;
goto v___jp_768_;
}
}
else
{
lean_dec(v_declName_764_);
return v___x_790_;
}
}
else
{
lean_dec(v_declName_764_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(lean_object* v_declName_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(lean_object* v_00_u03b1_853_, lean_object* v_msg_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_854_, v___y_855_, v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(lean_object* v_00_u03b1_859_, lean_object* v_msg_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(v_00_u03b1_859_, v_msg_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_864_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
}
#ifdef __cplusplus
}
#endif
