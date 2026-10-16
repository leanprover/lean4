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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcAny"};
static const lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_52_ = l_Lean_Environment_contains(v___x_51_, v_fst_49_, v___x_47_);
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
lean_object* v___y_66_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_75_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_76_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v___x_75_, v_s_64_);
v___x_77_ = lean_array_get_size(v___x_76_);
v___x_78_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_79_ = lean_nat_dec_lt(v___x_62_, v___x_77_);
if (v___x_79_ == 0)
{
lean_dec_ref(v___x_76_);
v___y_66_ = v___x_78_;
goto v___jp_65_;
}
else
{
size_t v___x_80_; size_t v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((size_t)0ULL);
v___x_81_ = lean_usize_of_nat(v___x_77_);
lean_inc_ref(v_env_63_);
v___x_82_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__2(v_env_63_, v___x_76_, v___x_80_, v___x_81_, v___x_78_);
lean_dec_ref(v___x_76_);
v___y_66_ = v___x_82_;
goto v___jp_65_;
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
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = ((size_t)0ULL);
v___x_72_ = lean_usize_of_nat(v___x_67_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__0(v_env_63_, v___y_66_, v___x_71_, v___x_72_, v___x_68_);
lean_inc_ref(v___x_73_);
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_ctor_set(v___x_74_, 2, v___y_66_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v___x_83_, lean_object* v_env_84_, lean_object* v_s_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(v___x_83_, v_env_84_, v_s_85_);
lean_dec(v_s_85_);
lean_dec(v___x_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; 
v___f_126_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_127_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_));
v___x_128_ = lean_box(0);
v___x_129_ = 0;
v___x_130_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_127_, v___x_128_, v___x_129_, v___f_126_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2____boxed(lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2_();
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(lean_object* v_init_133_, lean_object* v_t_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1_spec__1(v_init_133_, v_t_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_136_, lean_object* v_t_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1308376395____hygCtx___hyg_2__spec__1(v_init_136_, v_t_137_);
lean_dec(v_t_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(lean_object* v_type_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
lean_inc_ref(v_type_139_);
v___x_145_ = l_Lean_Meta_isProp(v_type_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; uint8_t v___x_147_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v___x_147_ = lean_unbox(v_a_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref_known(v___x_145_, 1);
v___x_148_ = l_Lean_Meta_isTypeFormerType(v_type_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
return v___x_148_;
}
else
{
lean_dec_ref(v_type_139_);
return v___x_145_;
}
}
else
{
lean_dec_ref(v_type_139_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0___boxed(lean_object* v_type_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___lam__0(v_type_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object* v_declName_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___f_161_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___closed__0));
v___x_162_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_163_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_162_, v___f_161_, v_declName_157_, v_a_158_, v_a_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f___boxed(lean_object* v_declName_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_declName_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* v_declName_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
v___x_174_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_173_, v_declName_169_, v_a_170_, v_a_171_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(lean_object* v_declName_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(lean_object* v_type_180_, lean_object* v_r_181_){
_start:
{
if (lean_obj_tag(v_type_180_) == 7)
{
lean_object* v_binderType_182_; lean_object* v_body_183_; lean_object* v___x_184_; 
v_binderType_182_ = lean_ctor_get(v_type_180_, 1);
lean_inc_ref(v_binderType_182_);
v_body_183_ = lean_ctor_get(v_type_180_, 2);
lean_inc_ref(v_body_183_);
lean_dec_ref_known(v_type_180_, 3);
v___x_184_ = lean_array_push(v_r_181_, v_binderType_182_);
v_type_180_ = v_body_183_;
v_r_181_ = v___x_184_;
goto _start;
}
else
{
lean_dec_ref(v_type_180_);
return v_r_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* v_type_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_190_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(v_type_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___f_196_; lean_object* v___x_2869__overap_197_; lean_object* v___x_198_; 
v___f_196_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0));
v___x_2869__overap_197_ = lean_panic_fn_borrowed(v___f_196_, v_msg_192_);
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
v___x_198_ = lean_apply_3(v___x_2869__overap_197_, v___y_193_, v___y_194_, lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v_msg_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_203_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType___closed__0(void){
_start:
{
lean_object* v___x_204_; lean_object* v_dummy_205_; 
v___x_204_ = lean_box(0);
v_dummy_205_ = l_Lean_Expr_sort___override(v___x_204_);
return v_dummy_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object* v_type_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_type_211_; 
v_type_211_ = l_Lean_Expr_headBeta(v_type_207_);
switch(lean_obj_tag(v_type_211_))
{
case 4:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParamTypes___closed__0));
v___x_213_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_type_211_, v___x_212_, v_a_208_, v_a_209_);
return v___x_213_;
}
case 5:
{
lean_object* v_dummy_214_; lean_object* v_nargs_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_dummy_214_ = lean_obj_once(&l_Lean_Compiler_LCNF_toMonoType___closed__0, &l_Lean_Compiler_LCNF_toMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_toMonoType___closed__0);
v_nargs_215_ = l_Lean_Expr_getAppNumArgs(v_type_211_);
lean_inc(v_nargs_215_);
v___x_216_ = lean_mk_array(v_nargs_215_, v_dummy_214_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_sub(v_nargs_215_, v___x_217_);
lean_dec(v_nargs_215_);
v___x_219_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_type_211_, v___x_216_, v___x_218_, v_a_208_, v_a_209_);
return v___x_219_;
}
case 7:
{
lean_object* v_binderName_220_; lean_object* v_binderType_221_; lean_object* v_body_222_; uint8_t v_binderInfo_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_binderName_220_ = lean_ctor_get(v_type_211_, 0);
lean_inc(v_binderName_220_);
v_binderType_221_ = lean_ctor_get(v_type_211_, 1);
lean_inc_ref(v_binderType_221_);
v_body_222_ = lean_ctor_get(v_type_211_, 2);
lean_inc_ref(v_body_222_);
v_binderInfo_223_ = lean_ctor_get_uint8(v_type_211_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_211_, 3);
v___x_224_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_225_ = lean_expr_instantiate1(v_body_222_, v___x_224_);
lean_dec_ref(v_body_222_);
v___x_226_ = l_Lean_Compiler_LCNF_toMonoType(v___x_225_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_253_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_253_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_253_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_253_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___y_232_; lean_object* v___y_233_; 
if (lean_obj_tag(v_a_227_) == 4)
{
lean_object* v_declName_244_; 
v_declName_244_ = lean_ctor_get(v_a_227_, 0);
if (lean_obj_tag(v_declName_244_) == 1)
{
lean_object* v_pre_245_; 
v_pre_245_ = lean_ctor_get(v_declName_244_, 0);
if (lean_obj_tag(v_pre_245_) == 0)
{
lean_object* v_str_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_str_246_ = lean_ctor_get(v_declName_244_, 1);
v___x_247_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_248_ = lean_string_dec_eq(v_str_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_del_object(v___x_229_);
v___y_232_ = v_a_208_;
v___y_233_ = v_a_209_;
goto v___jp_231_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec_ref_known(v_a_227_, 2);
lean_dec_ref(v_binderType_221_);
lean_dec(v_binderName_220_);
v___x_249_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_249_);
v___x_251_ = v___x_229_;
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
lean_del_object(v___x_229_);
v___y_232_ = v_a_208_;
v___y_233_ = v_a_209_;
goto v___jp_231_;
}
}
else
{
lean_del_object(v___x_229_);
v___y_232_ = v_a_208_;
v___y_233_ = v_a_209_;
goto v___jp_231_;
}
}
else
{
lean_del_object(v___x_229_);
v___y_232_ = v_a_208_;
v___y_233_ = v_a_209_;
goto v___jp_231_;
}
v___jp_231_:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_221_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_Expr_forallE___override(v_binderName_220_, v_a_235_, v_a_227_, v_binderInfo_223_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_dec(v_a_227_);
lean_dec(v_binderName_220_);
return v___x_234_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_221_);
lean_dec(v_binderName_220_);
return v___x_226_;
}
}
case 3:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref_known(v_type_211_, 1);
v___x_254_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
case 10:
{
lean_object* v_data_256_; lean_object* v_expr_257_; lean_object* v___x_258_; 
v_data_256_ = lean_ctor_get(v_type_211_, 0);
lean_inc(v_data_256_);
v_expr_257_ = lean_ctor_get(v_type_211_, 1);
lean_inc_ref(v_expr_257_);
lean_dec_ref_known(v_type_211_, 2);
v___x_258_ = l_Lean_Compiler_LCNF_toMonoType(v_expr_257_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = l_Lean_Expr_mdata___override(v_data_256_, v_a_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_dec(v_data_256_);
return v___x_258_;
}
}
default: 
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_type_211_);
v___x_268_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2));
v___x_274_ = lean_unsigned_to_nat(50u);
v___x_275_ = lean_unsigned_to_nat(81u);
v___x_276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1));
v___x_277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0));
v___x_278_ = l_mkPanicMessageWithDecl(v___x_277_, v___x_276_, v___x_275_, v___x_274_, v___x_273_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(lean_object* v_as_279_, size_t v_sz_280_, size_t v_i_281_, lean_object* v_b_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_a_287_; uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_lt(v_i_281_, v_sz_280_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v_b_282_);
return v___x_292_;
}
else
{
lean_object* v_fst_293_; lean_object* v_snd_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_342_; 
v_fst_293_ = lean_ctor_get(v_b_282_, 0);
v_snd_294_ = lean_ctor_get(v_b_282_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_b_282_);
if (v_isSharedCheck_342_ == 0)
{
v___x_296_ = v_b_282_;
v_isShared_297_ = v_isSharedCheck_342_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_snd_294_);
lean_inc(v_fst_293_);
lean_dec(v_b_282_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_342_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; 
lean_inc(v_snd_294_);
v___x_298_ = l_Lean_Expr_headBeta(v_snd_294_);
if (lean_obj_tag(v___x_298_) == 7)
{
lean_object* v_binderType_299_; lean_object* v_body_300_; lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v_result_304_; 
lean_dec(v_snd_294_);
v_binderType_299_ = lean_ctor_get(v___x_298_, 1);
lean_inc_ref(v_binderType_299_);
v_body_300_ = lean_ctor_get(v___x_298_, 2);
lean_inc_ref(v_body_300_);
lean_dec_ref_known(v___x_298_, 3);
v_a_301_ = lean_array_uget_borrowed(v_as_279_, v_i_281_);
lean_inc(v_a_301_);
v___x_302_ = l_Lean_Expr_headBeta(v_a_301_);
switch(lean_obj_tag(v_binderType_299_))
{
case 4:
{
lean_object* v_declName_324_; 
v_declName_324_ = lean_ctor_get(v_binderType_299_, 0);
lean_inc(v_declName_324_);
lean_dec_ref_known(v_binderType_299_, 2);
if (lean_obj_tag(v_declName_324_) == 1)
{
lean_object* v_pre_325_; 
v_pre_325_ = lean_ctor_get(v_declName_324_, 0);
if (lean_obj_tag(v_pre_325_) == 0)
{
lean_object* v_str_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_str_326_ = lean_ctor_get(v_declName_324_, 1);
lean_inc_ref(v_str_326_);
lean_dec_ref_known(v_declName_324_, 2);
v___x_327_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_328_ = lean_string_dec_eq(v_str_326_, v___x_327_);
lean_dec_ref(v_str_326_);
if (v___x_328_ == 0)
{
goto v___jp_321_;
}
else
{
goto v___jp_309_;
}
}
else
{
lean_dec_ref_known(v_declName_324_, 2);
goto v___jp_321_;
}
}
else
{
lean_dec(v_declName_324_);
goto v___jp_321_;
}
}
case 3:
{
lean_dec_ref_known(v_binderType_299_, 1);
goto v___jp_309_;
}
default: 
{
lean_dec_ref(v_binderType_299_);
goto v___jp_321_;
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_expr_instantiate1(v_body_300_, v___x_302_);
lean_dec_ref(v___x_302_);
lean_dec_ref(v_body_300_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_305_);
lean_ctor_set(v___x_296_, 0, v_result_304_);
v___x_307_ = v___x_296_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_result_304_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
v_a_287_ = v___x_307_;
goto v___jp_286_;
}
}
v___jp_309_:
{
lean_object* v___x_310_; 
lean_inc_ref(v___x_302_);
v___x_310_ = l_Lean_Compiler_LCNF_toMonoType(v___x_302_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = l_Lean_Expr_app___override(v_fst_293_, v_a_311_);
v_result_304_ = v___x_312_;
goto v___jp_303_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v___x_302_);
lean_dec_ref(v_body_300_);
lean_del_object(v___x_296_);
lean_dec(v_fst_293_);
v_a_313_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_310_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_323_ = l_Lean_Expr_app___override(v_fst_293_, v___x_322_);
v_result_304_ = v___x_323_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v___x_298_);
v___x_329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3);
v___x_330_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v___x_329_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_332_; 
lean_dec_ref_known(v___x_330_, 1);
if (v_isShared_297_ == 0)
{
v___x_332_ = v___x_296_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_fst_293_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_snd_294_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v_a_287_ = v___x_332_;
goto v___jp_286_;
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_del_object(v___x_296_);
lean_dec(v_snd_294_);
lean_dec(v_fst_293_);
v_a_334_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_330_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
v___jp_286_:
{
size_t v___x_288_; size_t v___x_289_; 
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_add(v_i_281_, v___x_288_);
v_i_281_ = v___x_289_;
v_b_282_ = v_a_287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* v_f_344_, lean_object* v_args_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
if (lean_obj_tag(v_f_344_) == 4)
{
lean_object* v_declName_349_; lean_object* v_us_350_; lean_object* v___x_351_; lean_object* v___y_353_; lean_object* v___y_354_; 
v_declName_349_ = lean_ctor_get(v_f_344_, 0);
lean_inc(v_declName_349_);
v_us_350_ = lean_ctor_get(v_f_344_, 1);
lean_inc(v_us_350_);
lean_dec_ref_known(v_f_344_, 2);
v___x_351_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_declName_349_) == 1)
{
lean_object* v_pre_414_; 
v_pre_414_ = lean_ctor_get(v_declName_349_, 0);
if (lean_obj_tag(v_pre_414_) == 0)
{
lean_object* v_str_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_str_415_ = lean_ctor_get(v_declName_349_, 1);
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_toMonoType___closed__1));
v___x_417_ = lean_string_dec_eq(v_str_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0));
v___x_419_ = lean_string_dec_eq(v_str_415_, v___x_418_);
if (v___x_419_ == 0)
{
v___y_353_ = v_a_346_;
v___y_354_ = v_a_347_;
goto v___jp_352_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref_known(v_declName_349_, 2);
lean_dec(v_us_350_);
lean_dec_ref(v_args_345_);
v___x_420_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref_known(v_declName_349_, 2);
lean_dec(v_us_350_);
lean_dec_ref(v_args_345_);
v___x_422_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
else
{
v___y_353_ = v_a_346_;
v___y_354_ = v_a_347_;
goto v___jp_352_;
}
}
else
{
v___y_353_ = v_a_346_;
v___y_354_ = v_a_347_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_355_; 
lean_inc(v_declName_349_);
v___x_355_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_349_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
if (lean_obj_tag(v_a_356_) == 1)
{
lean_object* v_val_357_; lean_object* v_ctorName_358_; lean_object* v_numParams_359_; lean_object* v_fieldIdx_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_us_350_);
lean_dec(v_declName_349_);
v_val_357_ = lean_ctor_get(v_a_356_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v_a_356_, 1);
v_ctorName_358_ = lean_ctor_get(v_val_357_, 0);
lean_inc(v_ctorName_358_);
v_numParams_359_ = lean_ctor_get(v_val_357_, 1);
lean_inc(v_numParams_359_);
v_fieldIdx_360_ = lean_ctor_get(v_val_357_, 2);
lean_inc(v_fieldIdx_360_);
lean_dec(v_val_357_);
v___x_361_ = lean_box(0);
v___x_362_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_358_, v___x_361_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = l_Array_toSubarray___redArg(v_args_345_, v___x_364_, v_numParams_359_);
v___x_366_ = l_Subarray_copy___redArg(v___x_365_);
v___x_367_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_363_, v___x_366_, v___y_353_, v___y_354_);
lean_dec_ref(v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_368_);
v___x_370_ = lean_array_get(v___x_351_, v___x_369_, v_fieldIdx_360_);
lean_dec(v_fieldIdx_360_);
lean_dec_ref(v___x_369_);
v___x_371_ = l_Lean_Compiler_LCNF_toMonoType(v___x_370_, v___y_353_, v___y_354_);
return v___x_371_;
}
else
{
lean_dec(v_fieldIdx_360_);
return v___x_367_;
}
}
else
{
lean_dec(v_fieldIdx_360_);
lean_dec(v_numParams_359_);
lean_dec_ref(v_args_345_);
return v___x_362_;
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_a_356_);
v___x_372_ = lean_box(0);
lean_inc(v_declName_349_);
v___x_373_ = l_Lean_mkConst(v_declName_349_, v___x_372_);
v___x_374_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_349_, v_us_350_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_405_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_405_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_405_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_405_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = l_Lean_Expr_isErased(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; size_t v_sz_381_; size_t v___x_382_; lean_object* v___x_383_; 
lean_del_object(v___x_377_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_373_);
lean_ctor_set(v___x_380_, 1, v_a_375_);
v_sz_381_ = lean_array_size(v_args_345_);
v___x_382_ = ((size_t)0ULL);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v_args_345_, v_sz_381_, v___x_382_, v___x_380_, v___y_353_, v___y_354_);
lean_dec_ref(v_args_345_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_fst_388_; lean_object* v___x_390_; 
v_fst_388_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_fst_388_);
lean_dec(v_a_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_fst_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_fst_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_383_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec(v_a_375_);
lean_dec_ref(v___x_373_);
lean_dec_ref(v_args_345_);
v___x_401_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_401_);
v___x_403_ = v___x_377_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_args_345_);
return v___x_374_;
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_us_350_);
lean_dec(v_declName_349_);
lean_dec_ref(v_args_345_);
v_a_406_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_355_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_355_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_args_345_);
lean_dec_ref(v_f_344_);
v___x_424_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
if (lean_obj_tag(v_x_426_) == 5)
{
lean_object* v_fn_432_; lean_object* v_arg_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_fn_432_ = lean_ctor_get(v_x_426_, 0);
lean_inc_ref(v_fn_432_);
v_arg_433_ = lean_ctor_get(v_x_426_, 1);
lean_inc_ref(v_arg_433_);
lean_dec_ref_known(v_x_426_, 2);
v___x_434_ = lean_array_set(v_x_427_, v_x_428_, v_arg_433_);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_sub(v_x_428_, v___x_435_);
lean_dec(v_x_428_);
v_x_426_ = v_fn_432_;
v_x_427_ = v___x_434_;
v_x_428_ = v___x_436_;
goto _start;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_x_428_);
v___x_438_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_x_426_, v_x_427_, v___y_429_, v___y_430_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(v_x_439_, v_x_440_, v_x_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___boxed(lean_object* v_type_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Compiler_LCNF_toMonoType(v_type_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object* v_as_451_, lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_sz_boxed_458_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_459_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v_as_451_, v_sz_boxed_458_, v_i_boxed_459_, v_b_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_as_451_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(lean_object* v_f_461_, lean_object* v_args_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_f_461_, v_args_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(lean_object* v_env_467_, lean_object* v_as_468_, size_t v_i_469_, size_t v_stop_470_, lean_object* v_b_471_){
_start:
{
lean_object* v___y_473_; uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_eq(v_i_469_, v_stop_470_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_fst_479_; uint8_t v___x_480_; 
v___x_478_ = lean_array_uget_borrowed(v_as_468_, v_i_469_);
v_fst_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_fst_479_);
lean_inc_ref(v_env_467_);
v___x_480_ = l_Lean_Environment_contains(v_env_467_, v_fst_479_, v___x_477_);
if (v___x_480_ == 0)
{
v___y_473_ = v_b_471_;
goto v___jp_472_;
}
else
{
lean_object* v___x_481_; 
lean_inc(v___x_478_);
v___x_481_ = lean_array_push(v_b_471_, v___x_478_);
v___y_473_ = v___x_481_;
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v_env_467_);
return v_b_471_;
}
v___jp_472_:
{
size_t v___x_474_; size_t v___x_475_; 
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_469_, v___x_474_);
v_i_469_ = v___x_475_;
v_b_471_ = v___y_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_482_, lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v_b_486_){
_start:
{
size_t v_i_boxed_487_; size_t v_stop_boxed_488_; lean_object* v_res_489_; 
v_i_boxed_487_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_488_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(v_env_482_, v_as_483_, v_i_boxed_487_, v_stop_boxed_488_, v_b_486_);
lean_dec_ref(v_as_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v_k_492_; lean_object* v_v_493_; lean_object* v_l_494_; lean_object* v_r_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_k_492_ = lean_ctor_get(v_x_491_, 1);
v_v_493_ = lean_ctor_get(v_x_491_, 2);
v_l_494_ = lean_ctor_get(v_x_491_, 3);
v_r_495_ = lean_ctor_get(v_x_491_, 4);
v___x_496_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_490_, v_l_494_);
lean_inc(v_v_493_);
lean_inc(v_k_492_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_k_492_);
lean_ctor_set(v___x_497_, 1, v_v_493_);
v___x_498_ = lean_array_push(v___x_496_, v___x_497_);
v_init_490_ = v___x_498_;
v_x_491_ = v_r_495_;
goto _start;
}
else
{
return v_init_490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_500_, v_x_501_);
lean_dec(v_x_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(lean_object* v_env_503_, lean_object* v_as_504_, size_t v_i_505_, size_t v_stop_506_, lean_object* v_b_507_){
_start:
{
lean_object* v___y_509_; uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_eq(v_i_505_, v_stop_506_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v_fst_515_; uint8_t v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_514_ = lean_array_uget_borrowed(v_as_504_, v_i_505_);
v_fst_515_ = lean_ctor_get(v___x_514_, 0);
v___x_516_ = 1;
lean_inc_ref(v_env_503_);
v___x_517_ = l_Lean_Environment_setExporting(v_env_503_, v___x_516_);
lean_inc(v_fst_515_);
v___x_518_ = l_Lean_Environment_contains(v___x_517_, v_fst_515_, v___x_513_);
if (v___x_518_ == 0)
{
v___y_509_ = v_b_507_;
goto v___jp_508_;
}
else
{
lean_object* v___x_519_; 
lean_inc(v___x_514_);
v___x_519_ = lean_array_push(v_b_507_, v___x_514_);
v___y_509_ = v___x_519_;
goto v___jp_508_;
}
}
else
{
lean_dec_ref(v_env_503_);
return v_b_507_;
}
v___jp_508_:
{
size_t v___x_510_; size_t v___x_511_; 
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_505_, v___x_510_);
v_i_505_ = v___x_511_;
v_b_507_ = v___y_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_520_, v_as_521_, v_i_boxed_525_, v_stop_boxed_526_, v_b_524_);
lean_dec_ref(v_as_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(lean_object* v_env_532_, lean_object* v_s_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___y_536_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__1_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_546_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v___x_545_, v_s_533_);
v___x_547_ = lean_array_get_size(v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_549_ = lean_nat_dec_lt(v___x_534_, v___x_547_);
if (v___x_549_ == 0)
{
lean_dec_ref(v___x_546_);
v___y_536_ = v___x_548_;
goto v___jp_535_;
}
else
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_547_);
lean_inc_ref(v_env_532_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__2(v_env_532_, v___x_546_, v___x_550_, v___x_551_, v___x_548_);
lean_dec_ref(v___x_546_);
v___y_536_ = v___x_552_;
goto v___jp_535_;
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_array_get_size(v___y_536_);
v___x_538_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_539_ = lean_nat_dec_lt(v___x_534_, v___x_537_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_env_532_);
v___x_540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___y_536_);
return v___x_540_;
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = ((size_t)0ULL);
v___x_542_ = lean_usize_of_nat(v___x_537_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__1(v_env_532_, v___y_536_, v___x_541_, v___x_542_, v___x_538_);
lean_inc_ref(v___x_543_);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_ctor_set(v___x_544_, 2, v___y_536_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_env_553_, lean_object* v_s_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(v_env_553_, v_s_554_);
lean_dec(v_s_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___f_564_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_));
v___x_566_ = lean_box(0);
v___x_567_ = 0;
v___x_568_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_565_, v___x_566_, v___x_567_, v___f_564_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2____boxed(lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2_();
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(lean_object* v_init_571_, lean_object* v_t_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0_spec__0(v_init_571_, v_t_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_574_, lean_object* v_t_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_735612717____hygCtx___hyg_2__spec__0(v_init_574_, v_t_575_);
lean_dec(v_t_575_);
return v_res_576_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__1);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object* v_declName_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_env_588_; lean_object* v___x_589_; lean_object* v_toEnvExtension_590_; lean_object* v_asyncMode_591_; uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_586_ = l_Lean_instInhabitedExpr;
v___x_587_ = lean_st_ref_get(v_a_584_);
v_env_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_590_ = lean_ctor_get(v___x_589_, 0);
v_asyncMode_591_ = lean_ctor_get(v_toEnvExtension_590_, 2);
v___x_592_ = 0;
lean_inc(v_declName_582_);
v___x_593_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_586_, v___x_589_, v_env_588_, v_declName_582_, v_asyncMode_591_, v___x_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 0;
v___x_595_ = lean_box(0);
lean_inc(v_declName_582_);
v___x_596_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_582_, v___x_595_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l_Lean_Compiler_LCNF_toMonoType(v_a_597_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_628_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_628_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_628_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_628_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v_env_604_; lean_object* v_nextMacroScope_605_; lean_object* v_ngen_606_; lean_object* v_auxDeclNGen_607_; lean_object* v_traceState_608_; lean_object* v_recordedDeps_609_; lean_object* v_messages_610_; lean_object* v_infoState_611_; lean_object* v_snapshotTasks_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_626_; 
v___x_603_ = lean_st_ref_take(v_a_584_);
v_env_604_ = lean_ctor_get(v___x_603_, 0);
v_nextMacroScope_605_ = lean_ctor_get(v___x_603_, 1);
v_ngen_606_ = lean_ctor_get(v___x_603_, 2);
v_auxDeclNGen_607_ = lean_ctor_get(v___x_603_, 3);
v_traceState_608_ = lean_ctor_get(v___x_603_, 4);
v_recordedDeps_609_ = lean_ctor_get(v___x_603_, 6);
v_messages_610_ = lean_ctor_get(v___x_603_, 7);
v_infoState_611_ = lean_ctor_get(v___x_603_, 8);
v_snapshotTasks_612_ = lean_ctor_get(v___x_603_, 9);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_603_, 5);
lean_dec(v_unused_627_);
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_626_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snapshotTasks_612_);
lean_inc(v_infoState_611_);
lean_inc(v_messages_610_);
lean_inc(v_recordedDeps_609_);
lean_inc(v_traceState_608_);
lean_inc(v_auxDeclNGen_607_);
lean_inc(v_ngen_606_);
lean_inc(v_nextMacroScope_605_);
lean_inc(v_env_604_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_626_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_616_ = lean_box(0);
v___x_617_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_589_, v_env_604_, v_declName_582_, v_a_599_, v___x_594_);
v___x_618_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 5, v___x_618_);
lean_ctor_set(v___x_614_, 0, v___x_617_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_nextMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_ngen_606_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_auxDeclNGen_607_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_traceState_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 6, v_recordedDeps_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 7, v_messages_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 8, v_infoState_611_);
lean_ctor_set(v_reuseFailAlloc_625_, 9, v_snapshotTasks_612_);
v___x_620_ = v_reuseFailAlloc_625_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = lean_st_ref_put(v_a_584_, v___x_620_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_616_);
v___x_623_ = v___x_601_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_616_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_declName_582_);
v_a_629_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_598_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_598_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_declName_582_);
v_a_637_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_596_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_596_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_declName_582_);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_653_);
v___x_646_ = v___x_593_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_593_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 0);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType___boxed(lean_object* v_declName_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_declName_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0(lean_object* v_declName_659_, lean_object* v_a_660_, lean_object* v_addEntryFn_661_, lean_object* v_ps_662_){
_start:
{
lean_object* v_importedEntries_663_; lean_object* v_state_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_importedEntries_663_ = lean_ctor_get(v_ps_662_, 0);
v_state_664_ = lean_ctor_get(v_ps_662_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_ps_662_);
if (v_isSharedCheck_673_ == 0)
{
v___x_666_ = v_ps_662_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_state_664_);
lean_inc(v_importedEntries_663_);
lean_dec(v_ps_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_declName_659_);
lean_ctor_set(v___x_668_, 1, v_a_660_);
v___x_669_ = lean_apply_2(v_addEntryFn_661_, v_state_664_, v___x_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_669_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_importedEntries_663_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__0);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_677_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
lean_ctor_set(v___x_679_, 3, v___x_678_);
lean_ctor_set(v___x_679_, 4, v___x_677_);
lean_ctor_set(v___x_679_, 5, v___x_677_);
lean_ctor_set(v___x_679_, 6, v___x_677_);
lean_ctor_set(v___x_679_, 7, v___x_677_);
lean_ctor_set(v___x_679_, 8, v___x_677_);
lean_ctor_set(v___x_679_, 9, v___x_677_);
lean_ctor_set(v___x_679_, 10, v___x_677_);
lean_ctor_set(v___x_679_, 11, v___x_676_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_unsigned_to_nat(32u);
v___x_681_ = lean_mk_empty_array_with_capacity(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = ((size_t)5ULL);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_unsigned_to_nat(32u);
v___x_686_ = lean_mk_empty_array_with_capacity(v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__2);
v___x_688_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_684_);
lean_ctor_set(v___x_688_, 3, v___x_684_);
lean_ctor_set_usize(v___x_688_, 4, v___x_683_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = lean_box(1);
v___x_690_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__3);
v___x_691_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__0);
v___x_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_689_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(lean_object* v_msgData_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_toCold_698_; lean_object* v_env_699_; lean_object* v_options_700_; uint8_t v___x_701_; lean_object* v_env_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_697_ = lean_st_ref_get(v___y_695_);
v_toCold_698_ = lean_ctor_get(v___y_694_, 0);
v_env_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc_ref(v_env_699_);
lean_dec(v___x_697_);
v_options_700_ = lean_ctor_get(v_toCold_698_, 2);
v___x_701_ = 0;
v_env_702_ = l_Lean_Environment_setRecordingDeps(v_env_699_, v___x_701_);
v___x_703_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__1);
v___x_704_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_700_);
v___x_705_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_705_, 0, v_env_702_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_704_);
lean_ctor_set(v___x_705_, 3, v_options_700_);
v___x_706_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_msgData_693_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0___boxed(lean_object* v_msgData_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msgData_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_ref_717_; lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_ref_717_ = lean_ctor_get(v___y_714_, 2);
v___x_718_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0_spec__0(v_msg_713_, v___y_714_, v___y_715_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_inc(v_ref_717_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_ref_717_);
lean_ctor_set(v___x_723_, 1, v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* v_declName_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_nextMacroScope_744_; lean_object* v_ngen_745_; lean_object* v_auxDeclNGen_746_; lean_object* v_traceState_747_; lean_object* v_recordedDeps_748_; lean_object* v_messages_749_; lean_object* v_infoState_750_; lean_object* v_snapshotTasks_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_env_790_; lean_object* v___x_791_; lean_object* v_toEnvExtension_792_; lean_object* v_asyncMode_793_; uint8_t v___x_794_; lean_object* v___x_795_; 
v___x_788_ = l_Lean_instInhabitedExpr;
v___x_789_ = lean_st_ref_get(v_a_741_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_env_790_);
lean_dec(v___x_789_);
v___x_791_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_792_ = lean_ctor_get(v___x_791_, 0);
v_asyncMode_793_ = lean_ctor_get(v_toEnvExtension_792_, 2);
v___x_794_ = 0;
lean_inc(v_declName_739_);
v___x_795_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_788_, v___x_791_, v_env_790_, v_declName_739_, v_asyncMode_793_, v___x_794_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_declName_739_);
v_val_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_val_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v_env_820_; uint8_t v___x_821_; lean_object* v___x_822_; 
lean_dec(v___x_795_);
v___x_804_ = lean_st_ref_get(v_a_741_);
v_env_820_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_820_);
lean_dec(v___x_804_);
v___x_821_ = 0;
lean_inc(v_declName_739_);
v___x_822_ = l_Lean_Environment_find_x3f(v_env_820_, v_declName_739_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 1)
{
lean_object* v_val_823_; 
v_val_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v___x_822_, 1);
switch(lean_obj_tag(v_val_823_))
{
case 5:
{
lean_dec_ref_known(v_val_823_, 1);
goto v___jp_805_;
}
case 6:
{
lean_dec_ref_known(v_val_823_, 1);
goto v___jp_805_;
}
default: 
{
lean_dec(v_val_823_);
v___y_760_ = v_a_740_;
v___y_761_ = v_a_741_;
goto v___jp_759_;
}
}
}
else
{
lean_dec(v___x_822_);
v___y_760_ = v_a_740_;
v___y_761_ = v_a_741_;
goto v___jp_759_;
}
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v___x_806_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1);
v___x_807_ = l_Lean_MessageData_ofName(v_declName_739_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3, &l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3_once, _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__3);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v___x_810_, v_a_740_, v_a_741_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
v___jp_743_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_obj_once(&l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2, &l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2_once, _init_l_Lean_Compiler_LCNF_setOtherDeclMonoType___closed__2);
v___x_756_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_756_, 0, v___y_754_);
lean_ctor_set(v___x_756_, 1, v_nextMacroScope_744_);
lean_ctor_set(v___x_756_, 2, v_ngen_745_);
lean_ctor_set(v___x_756_, 3, v_auxDeclNGen_746_);
lean_ctor_set(v___x_756_, 4, v_traceState_747_);
lean_ctor_set(v___x_756_, 5, v___x_755_);
lean_ctor_set(v___x_756_, 6, v_recordedDeps_748_);
lean_ctor_set(v___x_756_, 7, v_messages_749_);
lean_ctor_set(v___x_756_, 8, v_infoState_750_);
lean_ctor_set(v___x_756_, 9, v_snapshotTasks_751_);
v___x_757_ = lean_st_ref_put(v___y_753_, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___y_752_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(0);
lean_inc(v_declName_739_);
v___x_763_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_declName_739_, v___x_762_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_Compiler_LCNF_toMonoType(v_a_764_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v_env_768_; lean_object* v_nextMacroScope_769_; lean_object* v_ngen_770_; lean_object* v_auxDeclNGen_771_; lean_object* v_traceState_772_; lean_object* v_recordedDeps_773_; lean_object* v_messages_774_; lean_object* v_infoState_775_; lean_object* v_snapshotTasks_776_; lean_object* v___x_777_; lean_object* v_toEnvExtension_778_; lean_object* v_addEntryFn_779_; lean_object* v_asyncMode_780_; uint8_t v_logWrites_781_; lean_object* v___f_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc_n(v_a_766_, 2);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_st_ref_take(v___y_761_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref(v_env_768_);
v_nextMacroScope_769_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_nextMacroScope_769_);
v_ngen_770_ = lean_ctor_get(v___x_767_, 2);
lean_inc_ref(v_ngen_770_);
v_auxDeclNGen_771_ = lean_ctor_get(v___x_767_, 3);
lean_inc_ref(v_auxDeclNGen_771_);
v_traceState_772_ = lean_ctor_get(v___x_767_, 4);
lean_inc_ref(v_traceState_772_);
v_recordedDeps_773_ = lean_ctor_get(v___x_767_, 6);
lean_inc_ref(v_recordedDeps_773_);
v_messages_774_ = lean_ctor_get(v___x_767_, 7);
lean_inc_ref(v_messages_774_);
v_infoState_775_ = lean_ctor_get(v___x_767_, 8);
lean_inc_ref(v_infoState_775_);
v_snapshotTasks_776_ = lean_ctor_get(v___x_767_, 9);
lean_inc_ref(v_snapshotTasks_776_);
lean_dec(v___x_767_);
v___x_777_ = l_Lean_Compiler_LCNF_monoTypeExt;
v_toEnvExtension_778_ = lean_ctor_get(v___x_777_, 0);
v_addEntryFn_779_ = lean_ctor_get(v___x_777_, 3);
v_asyncMode_780_ = lean_ctor_get(v_toEnvExtension_778_, 2);
v_logWrites_781_ = lean_ctor_get_uint8(v_toEnvExtension_778_, sizeof(void*)*6);
lean_inc(v_addEntryFn_779_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lam__0), 4, 3);
lean_closure_set(v___f_782_, 0, v_declName_739_);
lean_closure_set(v___f_782_, 1, v_a_766_);
lean_closure_set(v___f_782_, 2, v_addEntryFn_779_);
v___x_783_ = lean_box(0);
v___x_784_ = 1;
if (v_logWrites_781_ == 0)
{
lean_object* v___x_785_; 
lean_inc_ref(v_toEnvExtension_778_);
v___x_785_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_778_, v_env_768_, v___f_782_, v_asyncMode_780_, v___x_783_, v___x_784_);
v_nextMacroScope_744_ = v_nextMacroScope_769_;
v_ngen_745_ = v_ngen_770_;
v_auxDeclNGen_746_ = v_auxDeclNGen_771_;
v_traceState_747_ = v_traceState_772_;
v_recordedDeps_748_ = v_recordedDeps_773_;
v_messages_749_ = v_messages_774_;
v_infoState_750_ = v_infoState_775_;
v_snapshotTasks_751_ = v_snapshotTasks_776_;
v___y_752_ = v_a_766_;
v___y_753_ = v___y_761_;
v___y_754_ = v___x_785_;
goto v___jp_743_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_inc_ref_n(v_toEnvExtension_778_, 2);
v___x_786_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_778_, v_env_768_);
lean_dec_ref(v_env_768_);
v___x_787_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_778_, v___x_786_, v___f_782_, v_asyncMode_780_, v___x_783_, v___x_784_);
v_nextMacroScope_744_ = v_nextMacroScope_769_;
v_ngen_745_ = v_ngen_770_;
v_auxDeclNGen_746_ = v_auxDeclNGen_771_;
v_traceState_747_ = v_traceState_772_;
v_recordedDeps_748_ = v_recordedDeps_773_;
v_messages_749_ = v_messages_774_;
v_infoState_750_ = v_infoState_775_;
v_snapshotTasks_751_ = v_snapshotTasks_776_;
v___y_752_ = v_a_766_;
v___y_753_ = v___y_761_;
v___y_754_ = v___x_787_;
goto v___jp_743_;
}
}
else
{
lean_dec(v_declName_739_);
return v___x_765_;
}
}
else
{
lean_dec(v_declName_739_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(lean_object* v_declName_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(lean_object* v_00_u03b1_829_, lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_msg_830_, v___y_831_, v___y_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(lean_object* v_00_u03b1_835_, lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(v_00_u03b1_835_, v_msg_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_840_;
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
