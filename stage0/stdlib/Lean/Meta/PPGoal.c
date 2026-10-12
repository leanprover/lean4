// Lean compiler output
// Module: Lean.Meta.PPGoal
// Imports: public import Lean.Meta.InferType
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Name_simpMacroScopes(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
uint8_t l_Lean_MetavarKind_isSyntheticOpaque(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "auxDecls"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 145, 51, 188, 89, 247, 104, 191)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "display auxiliary declarations used to compile recursive functions"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 146, 190, 114, 236, 223, 30, 15)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_auxDecls;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "implementationDetailHyps"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(95, 161, 54, 44, 105, 224, 181, 140)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "display implementation detail hypotheses in the local context"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(62, 255, 137, 94, 59, 236, 150, 82)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_implementationDetailHyps;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inaccessibleNames"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 160, 42, 6, 250, 122, 123, 232)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "display inaccessible declarations in the local context"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 204, 116, 106, 151, 53, 185, 129)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_inaccessibleNames;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showLetValues"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "always display let-declaration values in the info view"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 12, 21, 108, 66, 125, 244, 127)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 97, .m_data = "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 225, 32, 137, 29, 106, 114, 238)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues_threshold;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 21, 232, 108, 56, 195, 56, 160)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 235, 54, 94, 40, 62, 247, 246)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 115, .m_data = "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`, for tactic goals"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 176, 166, 194, 191, 152, 58, 125)}};
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(22, 125, 62, 189, 243, 139, 141, 137)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues_tactic_threshold;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object*);
static const lean_string_object l_Lean_Meta_getGoalPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⊢ "};
static const lean_object* l_Lean_Meta_getGoalPrefix___closed__0 = (const lean_object*)&l_Lean_Meta_getGoalPrefix___closed__0_value;
static const lean_string_object l_Lean_Meta_getGoalPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Meta_getGoalPrefix___closed__1 = (const lean_object*)&l_Lean_Meta_getGoalPrefix___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1_value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " :"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1_value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = " := ⋯"};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3_value;
static const lean_string_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5 = (const lean_object*)&l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ppGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l_Lean_Meta_ppGoal___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ppGoal___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ppGoal___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_ppGoal___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_ppGoal___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_ppGoal___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ppGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unknown goal"};
static const lean_object* l_Lean_Meta_ppGoal___closed__0 = (const lean_object*)&l_Lean_Meta_ppGoal___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ppGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_ppGoal___closed__0_value)}};
static const lean_object* l_Lean_Meta_ppGoal___closed__1 = (const lean_object*)&l_Lean_Meta_ppGoal___closed__1_value;
static const lean_ctor_object l_Lean_Meta_ppGoal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_ppGoal___closed__2 = (const lean_object*)&l_Lean_Meta_ppGoal___closed__2_value;
static const lean_ctor_object l_Lean_Meta_ppGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ppGoal___closed__2_value)}};
static const lean_object* l_Lean_Meta_ppGoal___closed__3 = (const lean_object*)&l_Lean_Meta_ppGoal___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
return v_res_60_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
return v_res_83_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_103_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_100_, v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_104_;
v_res_104_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
return v_res_106_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_124_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_126_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_123_, v___x_124_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_127_;
v_res_127_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
return v_res_129_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(lean_object* v_name_130_, lean_object* v_decl_131_, lean_object* v_ref_132_){
_start:
{
lean_object* v_defValue_134_; lean_object* v_descr_135_; lean_object* v_deprecation_x3f_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_defValue_134_ = lean_ctor_get(v_decl_131_, 0);
v_descr_135_ = lean_ctor_get(v_decl_131_, 1);
v_deprecation_x3f_136_ = lean_ctor_get(v_decl_131_, 2);
lean_inc(v_defValue_134_);
v___x_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_137_, 0, v_defValue_134_);
lean_inc(v_deprecation_x3f_136_);
lean_inc_ref(v_descr_135_);
lean_inc_n(v_name_130_, 2);
v___x_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_138_, 0, v_name_130_);
lean_ctor_set(v___x_138_, 1, v_ref_132_);
lean_ctor_set(v___x_138_, 2, v___x_137_);
lean_ctor_set(v___x_138_, 3, v_descr_135_);
lean_ctor_set(v___x_138_, 4, v_deprecation_x3f_136_);
v___x_139_ = lean_register_option(v_name_130_, v___x_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_139_, 0);
lean_dec(v_unused_148_);
v___x_141_ = v___x_139_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_dec(v___x_139_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_inc(v_defValue_134_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v_name_130_);
lean_ctor_set(v___x_143_, 1, v_defValue_134_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec(v_name_130_);
v_a_149_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_139_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_130_ = stack[0].m_obj;
lean_object* v_decl_131_ = stack[1].m_obj;
lean_object* v_ref_132_ = stack[2].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v_name_130_, v_decl_131_, v_ref_132_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_158_, lean_object* v_decl_159_, lean_object* v_ref_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v_name_158_, v_decl_159_, v_ref_160_);
lean_dec_ref(v_decl_159_);
return v_res_162_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_183_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_180_, v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_184_;
v_res_184_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
return v_res_186_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_209_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_206_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_210_;
v_res_210_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
return v_res_212_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(lean_object* v_opts_213_, lean_object* v_opt_214_){
_start:
{
lean_object* v_name_215_; lean_object* v_defValue_216_; lean_object* v_map_217_; lean_object* v___x_218_; 
v_name_215_ = lean_ctor_get(v_opt_214_, 0);
v_defValue_216_ = lean_ctor_get(v_opt_214_, 1);
v_map_217_ = lean_ctor_get(v_opts_213_, 0);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_217_, v_name_215_);
if (lean_obj_tag(v___x_218_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = lean_unbox(v_defValue_216_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; 
v_val_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v___x_218_, 1);
if (lean_obj_tag(v_val_220_) == 1)
{
uint8_t v_v_221_; 
v_v_221_ = lean_ctor_get_uint8(v_val_220_, 0);
lean_dec_ref_known(v_val_220_, 0);
return v_v_221_;
}
else
{
uint8_t v___x_222_; 
lean_dec(v_val_220_);
v___x_222_ = lean_unbox(v_defValue_216_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_213_ = stack[0].m_obj;
lean_object* v_opt_214_ = stack[1].m_obj;
uint8_t v_res_223_;
v_res_223_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_opts_213_, v_opt_214_);
stack->m_num = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0___boxed(lean_object* v_opts_224_, lean_object* v_opt_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_opts_224_, v_opt_225_);
lean_dec_ref(v_opt_225_);
lean_dec_ref(v_opts_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(lean_object* v_opts_228_, lean_object* v_opt_229_){
_start:
{
lean_object* v_name_230_; lean_object* v_defValue_231_; lean_object* v_map_232_; lean_object* v___x_233_; 
v_name_230_ = lean_ctor_get(v_opt_229_, 0);
v_defValue_231_ = lean_ctor_get(v_opt_229_, 1);
v_map_232_ = lean_ctor_get(v_opts_228_, 0);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_232_, v_name_230_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_inc(v_defValue_231_);
return v_defValue_231_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_233_, 1);
if (lean_obj_tag(v_val_234_) == 3)
{
lean_object* v_v_235_; 
v_v_235_ = lean_ctor_get(v_val_234_, 0);
lean_inc(v_v_235_);
lean_dec_ref_known(v_val_234_, 1);
return v_v_235_;
}
else
{
lean_dec(v_val_234_);
lean_inc(v_defValue_231_);
return v_defValue_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1___boxed(lean_object* v_opts_236_, lean_object* v_opt_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_opts_236_, v_opt_237_);
lean_dec_ref(v_opt_237_);
lean_dec_ref(v_opts_236_);
return v_res_238_;
}
}
lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(uint8_t v_tactic_239_, lean_object* v_e_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___y_244_; lean_object* v___y_251_; uint8_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = l_Lean_Expr_isAtomic(v_e_240_);
v___x_255_ = 1;
if (v___x_254_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_241_);
v___x_257_ = l_Lean_Meta_pp_showLetValues;
v___x_258_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___y_262_; 
v___x_259_ = l_Lean_Meta_pp_showLetValues_threshold;
v___x_260_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v___x_256_, v___x_259_);
if (v_tactic_239_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v___x_256_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___y_262_ = v___x_264_;
goto v___jp_261_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = l_Lean_Meta_pp_showLetValues_tactic_threshold;
v___x_266_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v___x_256_, v___x_265_);
lean_dec_ref(v___x_256_);
v___y_262_ = v___x_266_;
goto v___jp_261_;
}
v___jp_261_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_le(v___x_260_, v___y_262_);
if (v___x_263_ == 0)
{
lean_dec(v___y_262_);
v___y_251_ = v___x_260_;
goto v___jp_250_;
}
else
{
lean_dec(v___x_260_);
v___y_251_ = v___y_262_;
goto v___jp_250_;
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v___x_256_);
v___x_267_ = lean_box(v___x_255_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_box(v___x_255_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
v___jp_243_:
{
uint32_t v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = l_Lean_Expr_approxDepth(v_e_240_);
v___x_246_ = lean_uint32_to_nat(v___x_245_);
v___x_247_ = lean_nat_dec_le(v___x_246_, v___y_244_);
lean_dec(v___y_244_);
lean_dec(v___x_246_);
v___x_248_ = lean_box(v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
v___jp_250_:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(254u);
v___x_253_ = lean_nat_dec_le(v___x_252_, v___y_251_);
if (v___x_253_ == 0)
{
v___y_244_ = v___y_251_;
goto v___jp_243_;
}
else
{
lean_dec(v___y_251_);
v___y_244_ = v___x_252_;
goto v___jp_243_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ppGoal_shouldShowLetValue___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_tactic_239_ = stack[0].m_num;
lean_object* v_e_240_ = stack[1].m_obj;
lean_object* v_a_241_ = stack[2].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_239_, v_e_240_, v_a_241_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(lean_object* v_tactic_272_, lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_tactic_boxed_276_; lean_object* v_res_277_; 
v_tactic_boxed_276_ = lean_unbox(v_tactic_272_);
v_res_277_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_boxed_276_, v_e_273_, v_a_274_);
lean_dec_ref(v_a_274_);
lean_dec_ref(v_e_273_);
return v_res_277_;
}
}
lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue(uint8_t v_tactic_278_, lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_278_, v_e_279_, v_a_282_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Lean_Meta_ppGoal_shouldShowLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_tactic_278_ = stack[0].m_num;
lean_object* v_e_279_ = stack[1].m_obj;
lean_object* v_a_280_ = stack[2].m_obj;
lean_object* v_a_281_ = stack[3].m_obj;
lean_object* v_a_282_ = stack[4].m_obj;
lean_object* v_a_283_ = stack[5].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_Meta_ppGoal_shouldShowLetValue(v_tactic_278_, v_e_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(lean_object* v_tactic_287_, lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
uint8_t v_tactic_boxed_294_; lean_object* v_res_295_; 
v_tactic_boxed_294_ = lean_unbox(v_tactic_287_);
v_res_295_ = l_Lean_Meta_ppGoal_shouldShowLetValue(v_tactic_boxed_294_, v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec_ref(v_e_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object* v_fmt_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = l_Std_Format_isNil(v_fmt_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v_fmt_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
return v___x_302_;
}
else
{
return v_fmt_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object* v_mvarDecl_305_){
_start:
{
lean_object* v_type_306_; lean_object* v___x_307_; 
v_type_306_ = lean_ctor_get(v_mvarDecl_305_, 2);
v___x_307_ = l_Lean_isLHSGoal_x3f(v_type_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__0));
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__1));
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object* v_mvarDecl_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_310_);
lean_dec_ref(v_mvarDecl_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_dec(v_x_312_);
return v_x_313_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_328_; 
v_head_315_ = lean_ctor_get(v_x_314_, 0);
v_tail_316_ = lean_ctor_get(v_x_314_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_328_ == 0)
{
v___x_318_ = v_x_314_;
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_tail_316_);
lean_inc(v_head_315_);
lean_dec(v_x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
lean_inc(v_x_312_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 5);
lean_ctor_set(v___x_318_, 1, v_x_312_);
lean_ctor_set(v___x_318_, 0, v_x_313_);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_x_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_x_312_);
v___x_321_ = v_reuseFailAlloc_327_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = 1;
v___x_323_ = l_Lean_Name_toString(v_head_315_, v___x_322_);
v___x_324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_321_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v_x_313_ = v___x_325_;
v_x_314_ = v_tail_316_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v___x_331_; 
lean_dec(v_x_330_);
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
lean_object* v_tail_332_; 
v_tail_332_ = lean_ctor_get(v_x_329_, 1);
if (lean_obj_tag(v_tail_332_) == 0)
{
lean_object* v_head_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_x_330_);
v_head_333_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_head_333_);
lean_dec_ref_known(v_x_329_, 2);
v___x_334_ = 1;
v___x_335_ = l_Lean_Name_toString(v_head_333_, v___x_334_);
v___x_336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v_head_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_inc(v_tail_332_);
v_head_337_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_head_337_);
lean_dec_ref_known(v_x_329_, 2);
v___x_338_ = 1;
v___x_339_ = l_Lean_Name_toString(v_head_337_, v___x_338_);
v___x_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(v_x_330_, v___x_340_, v_tail_332_);
return v___x_341_;
}
}
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(lean_object* v_indent_348_, lean_object* v_ids_349_, lean_object* v_type_x3f_350_, lean_object* v_fmt_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = l_List_isEmpty___redArg(v_ids_349_);
if (v___x_357_ == 0)
{
lean_object* v_fmt_358_; 
v_fmt_358_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_fmt_351_);
if (lean_obj_tag(v_type_x3f_350_) == 0)
{
lean_object* v___x_359_; 
lean_dec(v_ids_349_);
lean_dec(v_indent_348_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_fmt_358_);
return v___x_359_;
}
else
{
lean_object* v_val_360_; lean_object* v___x_361_; 
v_val_360_ = lean_ctor_get(v_type_x3f_350_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v_type_x3f_350_, 1);
v___x_361_ = l_Lean_Meta_ppExpr(v_val_360_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_381_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_381_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_381_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_381_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_366_ = l_List_reverse___redArg(v_ids_349_);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1));
v___x_368_ = l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(v___x_366_, v___x_367_);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3));
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_box(1);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_362_);
v___x_373_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_373_, 0, v_indent_348_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_370_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = 0;
v___x_376_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_375_);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v_fmt_358_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_377_);
v___x_379_ = v___x_364_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_dec(v_fmt_358_);
lean_dec(v_ids_349_);
lean_dec(v_indent_348_);
return v___x_361_;
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec(v_type_x3f_350_);
lean_dec(v_ids_349_);
lean_dec(v_indent_348_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_fmt_351_);
return v___x_382_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_0interp(lean_interpreter_value* stack)
{
lean_object* v_indent_348_ = stack[0].m_obj;
lean_object* v_ids_349_ = stack[1].m_obj;
lean_object* v_type_x3f_350_ = stack[2].m_obj;
lean_object* v_fmt_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_a_353_ = stack[5].m_obj;
lean_object* v_a_354_ = stack[6].m_obj;
lean_object* v_a_355_ = stack[7].m_obj;
lean_object* v_res_383_;
v_res_383_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_348_, v_ids_349_, v_type_x3f_350_, v_fmt_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(lean_object* v_indent_384_, lean_object* v_ids_385_, lean_object* v_type_x3f_386_, lean_object* v_fmt_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_384_, v_ids_385_, v_type_x3f_386_, v_fmt_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(lean_object* v_e_394_, lean_object* v___y_395_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Expr_hasMVar(v_e_394_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_e_394_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v_mctx_400_; lean_object* v___x_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_404_; lean_object* v_cache_405_; lean_object* v_zetaDeltaFVarIds_406_; lean_object* v_postponed_407_; lean_object* v_diag_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
v___x_399_ = lean_st_ref_get(v___y_395_);
v_mctx_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_mctx_400_);
lean_dec(v___x_399_);
v___x_401_ = l_Lean_instantiateMVarsCore(v_mctx_400_, v_e_394_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_fst_402_);
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v___x_401_);
v___x_404_ = lean_st_ref_take(v___y_395_);
v_cache_405_ = lean_ctor_get(v___x_404_, 1);
v_zetaDeltaFVarIds_406_ = lean_ctor_get(v___x_404_, 2);
v_postponed_407_ = lean_ctor_get(v___x_404_, 3);
v_diag_408_ = lean_ctor_get(v___x_404_, 4);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_418_);
v___x_410_ = v___x_404_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_diag_408_);
lean_inc(v_postponed_407_);
lean_inc(v_zetaDeltaFVarIds_406_);
lean_inc(v_cache_405_);
lean_dec(v___x_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_snd_403_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_snd_403_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_cache_405_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_zetaDeltaFVarIds_406_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_postponed_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v_diag_408_);
v___x_413_ = v_reuseFailAlloc_416_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_st_ref_put(v___y_395_, v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v_fst_402_);
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_394_ = stack[0].m_obj;
lean_object* v___y_395_ = stack[1].m_obj;
lean_object* v_res_419_;
v_res_419_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_394_, v___y_395_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg___boxed(lean_object* v_e_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_420_, v___y_421_);
lean_dec(v___y_421_);
return v_res_423_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(lean_object* v_e_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_424_, v___y_426_);
return v___x_430_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_424_ = stack[0].m_obj;
lean_object* v___y_425_ = stack[1].m_obj;
lean_object* v___y_426_ = stack[2].m_obj;
lean_object* v___y_427_ = stack[3].m_obj;
lean_object* v___y_428_ = stack[4].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(v_e_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object* v_e_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(v_e_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
if (lean_obj_tag(v_x_440_) == 0)
{
uint8_t v___x_441_; 
v___x_441_ = 1;
return v___x_441_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
}
else
{
if (lean_obj_tag(v_x_440_) == 0)
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
else
{
lean_object* v_val_444_; lean_object* v_val_445_; uint8_t v___x_446_; 
v_val_444_ = lean_ctor_get(v_x_439_, 0);
v_val_445_ = lean_ctor_get(v_x_440_, 0);
v___x_446_ = lean_expr_eqv(v_val_444_, v_val_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_439_ = stack[0].m_obj;
lean_object* v_x_440_ = stack[1].m_obj;
uint8_t v_res_447_;
v_res_447_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_x_439_, v_x_440_);
stack->m_num = v_res_447_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_x_448_, v_x_449_);
lean_dec(v_x_449_);
lean_dec(v_x_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(lean_object* v_indent_461_, uint8_t v_tactic_462_, lean_object* v_varNames_463_, lean_object* v_prevType_x3f_464_, lean_object* v_fmt_465_, lean_object* v_localDecl_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
if (lean_obj_tag(v_localDecl_466_) == 0)
{
lean_object* v_userName_472_; lean_object* v_type_473_; lean_object* v_varName_474_; lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_515_; 
v_userName_472_ = lean_ctor_get(v_localDecl_466_, 2);
lean_inc(v_userName_472_);
v_type_473_ = lean_ctor_get(v_localDecl_466_, 3);
lean_inc_ref(v_type_473_);
lean_dec_ref_known(v_localDecl_466_, 4);
v_varName_474_ = l_Lean_Name_simpMacroScopes(v_userName_472_);
v___x_475_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_473_, v_a_468_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_515_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_515_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_515_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint8_t v___y_481_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_box(0);
v___x_512_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_464_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
lean_inc(v_a_476_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_476_);
v___x_514_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_464_, v___x_513_);
lean_dec_ref_known(v___x_513_, 1);
v___y_481_ = v___x_514_;
goto v___jp_480_;
}
else
{
v___y_481_ = v___x_512_;
goto v___jp_480_;
}
v___jp_480_:
{
if (v___y_481_ == 0)
{
lean_object* v___x_482_; 
lean_del_object(v___x_478_);
v___x_482_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_461_, v_varNames_463_, v_prevType_x3f_464_, v_fmt_465_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v_varName_474_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_a_476_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_a_483_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_488_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_493_ = v___x_485_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_a_476_);
lean_dec(v_varName_474_);
v_a_496_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_482_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_482_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec(v_prevType_x3f_464_);
lean_dec(v_indent_461_);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v_varName_474_);
lean_ctor_set(v___x_504_, 1, v_varNames_463_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v_a_476_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v_fmt_465_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_504_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_507_);
v___x_509_ = v___x_478_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
uint8_t v_nondep_516_; 
v_nondep_516_ = lean_ctor_get_uint8(v_localDecl_466_, sizeof(void*)*5);
if (v_nondep_516_ == 0)
{
lean_object* v_userName_517_; lean_object* v_type_518_; lean_object* v_value_519_; lean_object* v_varName_520_; lean_object* v___x_521_; 
v_userName_517_ = lean_ctor_get(v_localDecl_466_, 2);
lean_inc(v_userName_517_);
v_type_518_ = lean_ctor_get(v_localDecl_466_, 3);
lean_inc_ref(v_type_518_);
v_value_519_ = lean_ctor_get(v_localDecl_466_, 4);
lean_inc_ref(v_value_519_);
lean_dec_ref_known(v_localDecl_466_, 5);
v_varName_520_ = l_Lean_Name_simpMacroScopes(v_userName_517_);
lean_inc(v_indent_461_);
v___x_521_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_461_, v_varNames_463_, v_prevType_x3f_464_, v_fmt_465_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_586_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_586_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_586_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_586_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v_fmtElem_528_; lean_object* v___x_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_585_; 
v___x_526_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_522_);
v___x_539_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_518_, v_a_468_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_585_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_585_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_585_;
goto v_resetjp_541_;
}
v___jp_527_:
{
uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_529_ = 0;
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v_fmtElem_528_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_526_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_531_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_532_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_535_);
v___x_537_ = v___x_524_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
v_resetjp_541_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Meta_ppExpr(v_a_540_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = 1;
v___x_547_ = l_Lean_Name_toString(v_varName_520_, v___x_546_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 3);
lean_ctor_set(v___x_542_, 0, v___x_547_);
v___x_549_ = v___x_542_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_576_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v_a_556_; uint8_t v___x_557_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1));
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_a_545_);
v___x_553_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_value_519_, v_a_468_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_462_, v_a_554_, v_a_469_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = lean_unbox(v_a_556_);
lean_dec(v_a_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_a_554_);
lean_dec(v_indent_461_);
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3));
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_552_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v_fmtElem_528_ = v___x_559_;
goto v___jp_527_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_ppExpr(v_a_554_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5));
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_552_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_box(1);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v_a_561_);
v___x_566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_566_, 0, v_indent_461_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v_fmtElem_528_ = v___x_567_;
goto v___jp_527_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref_known(v___x_552_, 2);
lean_dec(v___x_526_);
lean_del_object(v___x_524_);
lean_dec(v_indent_461_);
v_a_568_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_560_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_560_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_del_object(v___x_542_);
lean_dec(v___x_526_);
lean_del_object(v___x_524_);
lean_dec(v_varName_520_);
lean_dec_ref(v_value_519_);
lean_dec(v_indent_461_);
v_a_577_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_544_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_544_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_varName_520_);
lean_dec_ref(v_value_519_);
lean_dec_ref(v_type_518_);
lean_dec(v_indent_461_);
v_a_587_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_521_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_521_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_userName_595_; lean_object* v_type_596_; lean_object* v_varName_597_; lean_object* v___x_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_638_; 
v_userName_595_ = lean_ctor_get(v_localDecl_466_, 2);
lean_inc(v_userName_595_);
v_type_596_ = lean_ctor_get(v_localDecl_466_, 3);
lean_inc_ref(v_type_596_);
lean_dec_ref_known(v_localDecl_466_, 5);
v_varName_597_ = l_Lean_Name_simpMacroScopes(v_userName_595_);
v___x_598_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_596_, v_a_468_);
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_638_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_638_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_638_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___y_604_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_464_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
lean_inc(v_a_599_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_a_599_);
v___x_637_ = l_instBEqOption_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_464_, v___x_636_);
lean_dec_ref_known(v___x_636_, 1);
v___y_604_ = v___x_637_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_635_;
goto v___jp_603_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_object* v___x_605_; 
lean_del_object(v___x_601_);
v___x_605_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_461_, v_varNames_463_, v_prevType_x3f_464_, v_fmt_465_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_618_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v_varName_597_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_a_599_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_a_606_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_614_);
v___x_616_ = v___x_608_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_a_599_);
lean_dec(v_varName_597_);
v_a_619_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_605_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_605_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v_prevType_x3f_464_);
lean_dec(v_indent_461_);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v_varName_597_);
lean_ctor_set(v___x_627_, 1, v_varNames_463_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v_a_599_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_fmt_465_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_627_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_630_);
v___x_632_ = v___x_601_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_indent_461_ = stack[0].m_obj;
uint8_t v_tactic_462_ = stack[1].m_num;
lean_object* v_varNames_463_ = stack[2].m_obj;
lean_object* v_prevType_x3f_464_ = stack[3].m_obj;
lean_object* v_fmt_465_ = stack[4].m_obj;
lean_object* v_localDecl_466_ = stack[5].m_obj;
lean_object* v_a_467_ = stack[6].m_obj;
lean_object* v_a_468_ = stack[7].m_obj;
lean_object* v_a_469_ = stack[8].m_obj;
lean_object* v_a_470_ = stack[9].m_obj;
lean_object* v_res_639_;
v_res_639_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v_indent_461_, v_tactic_462_, v_varNames_463_, v_prevType_x3f_464_, v_fmt_465_, v_localDecl_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___boxed(lean_object* v_indent_640_, lean_object* v_tactic_641_, lean_object* v_varNames_642_, lean_object* v_prevType_x3f_643_, lean_object* v_fmt_644_, lean_object* v_localDecl_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_tactic_boxed_651_; lean_object* v_res_652_; 
v_tactic_boxed_651_ = lean_unbox(v_tactic_641_);
v_res_652_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v_indent_640_, v_tactic_boxed_651_, v_varNames_642_, v_prevType_x3f_643_, v_fmt_644_, v_localDecl_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_652_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(lean_object* v_lctx_653_, lean_object* v_localInsts_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_653_, v_localInsts_654_, v_x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_661_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_653_ = stack[0].m_obj;
lean_object* v_localInsts_654_ = stack[1].m_obj;
lean_object* v_x_655_ = stack[2].m_obj;
lean_object* v___y_656_ = stack[3].m_obj;
lean_object* v___y_657_ = stack[4].m_obj;
lean_object* v___y_658_ = stack[5].m_obj;
lean_object* v___y_659_ = stack[6].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_653_, v_localInsts_654_, v_x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg___boxed(lean_object* v_lctx_679_, lean_object* v_localInsts_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_679_, v_localInsts_680_, v_x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(lean_object* v_00_u03b1_688_, lean_object* v_lctx_689_, lean_object* v_localInsts_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_689_, v_localInsts_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_689_ = stack[1].m_obj;
lean_object* v_localInsts_690_ = stack[2].m_obj;
lean_object* v_x_691_ = stack[3].m_obj;
lean_object* v___y_692_ = stack[4].m_obj;
lean_object* v___y_693_ = stack[5].m_obj;
lean_object* v___y_694_ = stack[6].m_obj;
lean_object* v___y_695_ = stack[7].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(lean_box(0), v_lctx_689_, v_localInsts_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___boxed(lean_object* v_00_u03b1_699_, lean_object* v_lctx_700_, lean_object* v_localInsts_701_, lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(v_00_u03b1_699_, v_lctx_700_, v_localInsts_701_, v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_708_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_nat_to_int(v___x_709_);
return v___x_710_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(uint8_t v___x_711_, uint8_t v___x_712_, uint8_t v___x_713_, lean_object* v_as_714_, size_t v_i_715_, size_t v_stop_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_a_724_; lean_object* v___y_729_; uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_eq(v_i_715_, v_stop_716_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_array_uget_borrowed(v_as_714_, v_i_715_);
if (lean_obj_tag(v___x_732_) == 0)
{
v_a_724_ = v_b_717_;
goto v___jp_723_;
}
else
{
lean_object* v_snd_733_; lean_object* v_val_734_; lean_object* v_fst_735_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_738_; 
v_snd_733_ = lean_ctor_get(v_b_717_, 1);
v_val_734_ = lean_ctor_get(v___x_732_, 0);
v_fst_735_ = lean_ctor_get(v_b_717_, 0);
v_fst_736_ = lean_ctor_get(v_snd_733_, 0);
v_snd_737_ = lean_ctor_get(v_snd_733_, 1);
v___x_738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
if (v___x_713_ == 0)
{
uint8_t v___x_743_; 
v___x_743_ = l_Lean_LocalDecl_isAuxDecl(v_val_734_);
if (v___x_743_ == 0)
{
goto v___jp_739_;
}
else
{
v_a_724_ = v_b_717_;
goto v___jp_723_;
}
}
else
{
goto v___jp_739_;
}
v___jp_739_:
{
if (v___x_711_ == 0)
{
uint8_t v___x_740_; 
v___x_740_ = l_Lean_LocalDecl_isImplementationDetail(v_val_734_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_inc(v_fst_735_);
lean_dec_ref(v_b_717_);
lean_inc(v_val_734_);
v___x_741_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_738_, v___x_712_, v_fst_735_, v_fst_736_, v_snd_737_, v_val_734_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
v___y_729_ = v___x_741_;
goto v___jp_728_;
}
else
{
v_a_724_ = v_b_717_;
goto v___jp_723_;
}
}
else
{
lean_object* v___x_742_; 
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_inc(v_fst_735_);
lean_dec_ref(v_b_717_);
lean_inc(v_val_734_);
v___x_742_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_738_, v___x_712_, v_fst_735_, v_fst_736_, v_snd_737_, v_val_734_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
v___y_729_ = v___x_742_;
goto v___jp_728_;
}
}
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_b_717_);
return v___x_744_;
}
v___jp_723_:
{
size_t v___x_725_; size_t v___x_726_; 
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_715_, v___x_725_);
v_i_715_ = v___x_726_;
v_b_717_ = v_a_724_;
goto _start;
}
v___jp_728_:
{
if (lean_obj_tag(v___y_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___y_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___y_729_, 1);
v_a_724_ = v_a_730_;
goto v___jp_723_;
}
else
{
return v___y_729_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_711_ = stack[0].m_num;
uint8_t v___x_712_ = stack[1].m_num;
uint8_t v___x_713_ = stack[2].m_num;
lean_object* v_as_714_ = stack[3].m_obj;
size_t v_i_715_ = stack[4].m_num;
size_t v_stop_716_ = stack[5].m_num;
lean_object* v_b_717_ = stack[6].m_obj;
lean_object* v___y_718_ = stack[7].m_obj;
lean_object* v___y_719_ = stack[8].m_obj;
lean_object* v___y_720_ = stack[9].m_obj;
lean_object* v___y_721_ = stack[10].m_obj;
lean_object* v_res_745_;
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_711_, v___x_712_, v___x_713_, v_as_714_, v_i_715_, v_stop_716_, v_b_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v___x_4467__boxed_758_; uint8_t v___x_4468__boxed_759_; uint8_t v___x_4469__boxed_760_; size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v___x_4467__boxed_758_ = lean_unbox(v___x_746_);
v___x_4468__boxed_759_ = lean_unbox(v___x_747_);
v___x_4469__boxed_760_ = lean_unbox(v___x_748_);
v_i_boxed_761_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_4467__boxed_758_, v___x_4468__boxed_759_, v___x_4469__boxed_760_, v_as_749_, v_i_boxed_761_, v_stop_boxed_762_, v_b_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v_as_749_);
return v_res_763_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(uint8_t v___x_764_, uint8_t v___x_765_, uint8_t v___x_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v_cs_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_787_; 
v_cs_774_ = lean_ctor_get(v_x_767_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_787_ == 0)
{
v___x_776_ = v_x_767_;
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_cs_774_);
lean_dec(v_x_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_array_get_size(v_cs_774_);
v___x_780_ = lean_nat_dec_lt(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v_cs_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_x_768_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_x_768_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_776_);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_779_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_764_, v___x_765_, v___x_766_, v_cs_774_, v___x_784_, v___x_785_, v_x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec_ref(v_cs_774_);
return v___x_786_;
}
}
}
else
{
lean_object* v_vs_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_801_; 
v_vs_788_ = lean_ctor_get(v_x_767_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_801_ == 0)
{
v___x_790_ = v_x_767_;
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_vs_788_);
lean_dec(v_x_767_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_array_get_size(v_vs_788_);
v___x_794_ = lean_nat_dec_lt(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
lean_dec_ref(v_vs_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
lean_ctor_set(v___x_790_, 0, v_x_768_);
v___x_796_ = v___x_790_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_x_768_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_790_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_793_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_764_, v___x_765_, v___x_766_, v_vs_788_, v___x_798_, v___x_799_, v_x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec_ref(v_vs_788_);
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_764_ = stack[0].m_num;
uint8_t v___x_765_ = stack[1].m_num;
uint8_t v___x_766_ = stack[2].m_num;
lean_object* v_x_767_ = stack[3].m_obj;
lean_object* v_x_768_ = stack[4].m_obj;
lean_object* v___y_769_ = stack[5].m_obj;
lean_object* v___y_770_ = stack[6].m_obj;
lean_object* v___y_771_ = stack[7].m_obj;
lean_object* v___y_772_ = stack[8].m_obj;
lean_object* v_res_802_;
v_res_802_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_764_, v___x_765_, v___x_766_, v_x_767_, v_x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
stack->m_obj
 = v_res_802_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(uint8_t v___x_803_, uint8_t v___x_804_, uint8_t v___x_805_, lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_eq(v_i_807_, v_stop_808_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_array_uget_borrowed(v_as_806_, v_i_807_);
lean_inc(v___x_816_);
v___x_817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_803_, v___x_804_, v___x_805_, v___x_816_, v_b_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; size_t v___x_819_; size_t v___x_820_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_807_, v___x_819_);
v_i_807_ = v___x_820_;
v_b_809_ = v_a_818_;
goto _start;
}
else
{
return v___x_817_;
}
}
else
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_b_809_);
return v___x_822_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_803_ = stack[0].m_num;
uint8_t v___x_804_ = stack[1].m_num;
uint8_t v___x_805_ = stack[2].m_num;
lean_object* v_as_806_ = stack[3].m_obj;
size_t v_i_807_ = stack[4].m_num;
size_t v_stop_808_ = stack[5].m_num;
lean_object* v_b_809_ = stack[6].m_obj;
lean_object* v___y_810_ = stack[7].m_obj;
lean_object* v___y_811_ = stack[8].m_obj;
lean_object* v___y_812_ = stack[9].m_obj;
lean_object* v___y_813_ = stack[10].m_obj;
lean_object* v_res_823_;
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_803_, v___x_804_, v___x_805_, v_as_806_, v_i_807_, v_stop_808_, v_b_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_4578__boxed_836_; uint8_t v___x_4579__boxed_837_; uint8_t v___x_4580__boxed_838_; size_t v_i_boxed_839_; size_t v_stop_boxed_840_; lean_object* v_res_841_; 
v___x_4578__boxed_836_ = lean_unbox(v___x_824_);
v___x_4579__boxed_837_ = lean_unbox(v___x_825_);
v___x_4580__boxed_838_ = lean_unbox(v___x_826_);
v_i_boxed_839_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_840_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_4578__boxed_836_, v___x_4579__boxed_837_, v___x_4580__boxed_838_, v_as_827_, v_i_boxed_839_, v_stop_boxed_840_, v_b_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v_as_827_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(lean_object* v___x_842_, lean_object* v___x_843_, lean_object* v___x_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_4595__boxed_852_; uint8_t v___x_4596__boxed_853_; uint8_t v___x_4597__boxed_854_; lean_object* v_res_855_; 
v___x_4595__boxed_852_ = lean_unbox(v___x_842_);
v___x_4596__boxed_853_ = lean_unbox(v___x_843_);
v___x_4597__boxed_854_ = lean_unbox(v___x_844_);
v_res_855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_4595__boxed_852_, v___x_4596__boxed_853_, v___x_4597__boxed_854_, v_x_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_855_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_856_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(uint8_t v___x_857_, uint8_t v___x_858_, uint8_t v___x_859_, lean_object* v_x_860_, size_t v_x_861_, size_t v_x_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_object* v_cs_869_; lean_object* v___x_870_; size_t v___x_871_; lean_object* v_j_872_; lean_object* v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v_cs_869_ = lean_ctor_get(v_x_860_, 0);
lean_inc_ref(v_cs_869_);
lean_dec_ref_known(v_x_860_, 1);
v___x_870_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0);
v___x_871_ = lean_usize_shift_right(v_x_861_, v_x_862_);
v_j_872_ = lean_usize_to_nat(v___x_871_);
v___x_873_ = lean_array_get_borrowed(v___x_870_, v_cs_869_, v_j_872_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_shift_left(v___x_874_, v_x_862_);
v___x_876_ = lean_usize_sub(v___x_875_, v___x_874_);
v___x_877_ = lean_usize_land(v_x_861_, v___x_876_);
v___x_878_ = ((size_t)5ULL);
v___x_879_ = lean_usize_sub(v_x_862_, v___x_878_);
lean_inc(v___x_873_);
v___x_880_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_857_, v___x_858_, v___x_859_, v___x_873_, v___x_877_, v___x_879_, v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_j_872_, v___x_882_);
lean_dec(v_j_872_);
v___x_884_ = lean_array_get_size(v_cs_869_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec(v___x_883_);
lean_dec_ref(v_cs_869_);
return v___x_880_;
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_886_ = lean_usize_of_nat(v___x_883_);
lean_dec(v___x_883_);
v___x_887_ = lean_usize_of_nat(v___x_884_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_857_, v___x_858_, v___x_859_, v_cs_869_, v___x_886_, v___x_887_, v_a_881_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec_ref(v_cs_869_);
return v___x_888_;
}
}
else
{
lean_dec(v_j_872_);
lean_dec_ref(v_cs_869_);
return v___x_880_;
}
}
else
{
lean_object* v_vs_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_902_; 
v_vs_889_ = lean_ctor_get(v_x_860_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_902_ == 0)
{
v___x_891_ = v_x_860_;
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_vs_889_);
lean_dec(v_x_860_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_usize_to_nat(v_x_861_);
v___x_894_ = lean_array_get_size(v_vs_889_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v___x_893_);
lean_dec_ref(v_vs_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v_x_863_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_x_863_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
lean_del_object(v___x_891_);
v___x_899_ = lean_usize_of_nat(v___x_893_);
lean_dec(v___x_893_);
v___x_900_ = lean_usize_of_nat(v___x_894_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_857_, v___x_858_, v___x_859_, v_vs_889_, v___x_899_, v___x_900_, v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec_ref(v_vs_889_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_857_ = stack[0].m_num;
uint8_t v___x_858_ = stack[1].m_num;
uint8_t v___x_859_ = stack[2].m_num;
lean_object* v_x_860_ = stack[3].m_obj;
size_t v_x_861_ = stack[4].m_num;
size_t v_x_862_ = stack[5].m_num;
lean_object* v_x_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v___y_865_ = stack[8].m_obj;
lean_object* v___y_866_ = stack[9].m_obj;
lean_object* v___y_867_ = stack[10].m_obj;
lean_object* v_res_903_;
v_res_903_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_857_, v___x_858_, v___x_859_, v_x_860_, v_x_861_, v_x_862_, v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_4779__boxed_916_; uint8_t v___x_4780__boxed_917_; uint8_t v___x_4781__boxed_918_; size_t v_x_4783__boxed_919_; size_t v_x_4784__boxed_920_; lean_object* v_res_921_; 
v___x_4779__boxed_916_ = lean_unbox(v___x_904_);
v___x_4780__boxed_917_ = lean_unbox(v___x_905_);
v___x_4781__boxed_918_ = lean_unbox(v___x_906_);
v_x_4783__boxed_919_ = lean_unbox_usize(v_x_908_);
lean_dec(v_x_908_);
v_x_4784__boxed_920_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_res_921_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_4779__boxed_916_, v___x_4780__boxed_917_, v___x_4781__boxed_918_, v_x_907_, v_x_4783__boxed_919_, v_x_4784__boxed_920_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_921_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(uint8_t v___x_922_, uint8_t v___x_923_, uint8_t v___x_924_, lean_object* v_t_925_, lean_object* v_init_926_, lean_object* v_start_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_nat_dec_eq(v_start_927_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v_root_935_; lean_object* v_tail_936_; size_t v_shift_937_; lean_object* v_tailOff_938_; uint8_t v___x_939_; 
v_root_935_ = lean_ctor_get(v_t_925_, 0);
lean_inc_ref(v_root_935_);
v_tail_936_ = lean_ctor_get(v_t_925_, 1);
lean_inc_ref(v_tail_936_);
v_shift_937_ = lean_ctor_get_usize(v_t_925_, 4);
v_tailOff_938_ = lean_ctor_get(v_t_925_, 3);
lean_inc(v_tailOff_938_);
lean_dec_ref(v_t_925_);
v___x_939_ = lean_nat_dec_le(v_tailOff_938_, v_start_927_);
if (v___x_939_ == 0)
{
size_t v___x_940_; lean_object* v___x_941_; 
lean_dec(v_tailOff_938_);
v___x_940_ = lean_usize_of_nat(v_start_927_);
v___x_941_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_922_, v___x_923_, v___x_924_, v_root_935_, v___x_940_, v_shift_937_, v_init_926_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v___x_943_ = lean_array_get_size(v_tail_936_);
v___x_944_ = lean_nat_dec_lt(v___x_933_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_tail_936_);
return v___x_941_;
}
else
{
size_t v___x_945_; size_t v___x_946_; lean_object* v___x_947_; 
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_945_ = ((size_t)0ULL);
v___x_946_ = lean_usize_of_nat(v___x_943_);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_922_, v___x_923_, v___x_924_, v_tail_936_, v___x_945_, v___x_946_, v_a_942_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v_tail_936_);
return v___x_947_;
}
}
else
{
lean_dec_ref(v_tail_936_);
return v___x_941_;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
lean_dec_ref(v_root_935_);
v___x_948_ = lean_nat_sub(v_start_927_, v_tailOff_938_);
lean_dec(v_tailOff_938_);
v___x_949_ = lean_array_get_size(v_tail_936_);
v___x_950_ = lean_nat_dec_lt(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec(v___x_948_);
lean_dec_ref(v_tail_936_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_init_926_);
return v___x_951_;
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_usize_of_nat(v___x_948_);
lean_dec(v___x_948_);
v___x_953_ = lean_usize_of_nat(v___x_949_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_922_, v___x_923_, v___x_924_, v_tail_936_, v___x_952_, v___x_953_, v_init_926_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v_tail_936_);
return v___x_954_;
}
}
}
else
{
lean_object* v_root_955_; lean_object* v_tail_956_; lean_object* v___x_957_; 
v_root_955_ = lean_ctor_get(v_t_925_, 0);
lean_inc_ref(v_root_955_);
v_tail_956_ = lean_ctor_get(v_t_925_, 1);
lean_inc_ref(v_tail_956_);
lean_dec_ref(v_t_925_);
v___x_957_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_922_, v___x_923_, v___x_924_, v_root_955_, v_init_926_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v___x_959_ = lean_array_get_size(v_tail_956_);
v___x_960_ = lean_nat_dec_lt(v___x_933_, v___x_959_);
if (v___x_960_ == 0)
{
lean_dec_ref(v_tail_956_);
return v___x_957_;
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_959_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_922_, v___x_923_, v___x_924_, v_tail_956_, v___x_961_, v___x_962_, v_a_958_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v_tail_956_);
return v___x_963_;
}
}
else
{
lean_dec_ref(v_tail_956_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_922_ = stack[0].m_num;
uint8_t v___x_923_ = stack[1].m_num;
uint8_t v___x_924_ = stack[2].m_num;
lean_object* v_t_925_ = stack[3].m_obj;
lean_object* v_init_926_ = stack[4].m_obj;
lean_object* v_start_927_ = stack[5].m_obj;
lean_object* v___y_928_ = stack[6].m_obj;
lean_object* v___y_929_ = stack[7].m_obj;
lean_object* v___y_930_ = stack[8].m_obj;
lean_object* v___y_931_ = stack[9].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_922_, v___x_923_, v___x_924_, v_t_925_, v_init_926_, v_start_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v_t_968_, lean_object* v_init_969_, lean_object* v_start_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v___x_4941__boxed_976_; uint8_t v___x_4942__boxed_977_; uint8_t v___x_4943__boxed_978_; lean_object* v_res_979_; 
v___x_4941__boxed_976_ = lean_unbox(v___x_965_);
v___x_4942__boxed_977_ = lean_unbox(v___x_966_);
v___x_4943__boxed_978_ = lean_unbox(v___x_967_);
v_res_979_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_4941__boxed_976_, v___x_4942__boxed_977_, v___x_4943__boxed_978_, v_t_968_, v_init_969_, v_start_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v_start_970_);
return v_res_979_;
}
}
lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(uint8_t v___x_980_, uint8_t v___x_981_, uint8_t v___x_982_, lean_object* v_lctx_983_, lean_object* v_init_984_, lean_object* v_start_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_decls_991_; lean_object* v___x_992_; 
v_decls_991_ = lean_ctor_get(v_lctx_983_, 1);
lean_inc_ref(v_decls_991_);
lean_dec_ref(v_lctx_983_);
v___x_992_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_980_, v___x_981_, v___x_982_, v_decls_991_, v_init_984_, v_start_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_992_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_980_ = stack[0].m_num;
uint8_t v___x_981_ = stack[1].m_num;
uint8_t v___x_982_ = stack[2].m_num;
lean_object* v_lctx_983_ = stack[3].m_obj;
lean_object* v_init_984_ = stack[4].m_obj;
lean_object* v_start_985_ = stack[5].m_obj;
lean_object* v___y_986_ = stack[6].m_obj;
lean_object* v___y_987_ = stack[7].m_obj;
lean_object* v___y_988_ = stack[8].m_obj;
lean_object* v___y_989_ = stack[9].m_obj;
lean_object* v_res_993_;
v_res_993_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_980_, v___x_981_, v___x_982_, v_lctx_983_, v_init_984_, v_start_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(lean_object* v___x_994_, lean_object* v___x_995_, lean_object* v___x_996_, lean_object* v_lctx_997_, lean_object* v_init_998_, lean_object* v_start_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_5058__boxed_1005_; uint8_t v___x_5059__boxed_1006_; uint8_t v___x_5060__boxed_1007_; lean_object* v_res_1008_; 
v___x_5058__boxed_1005_ = lean_unbox(v___x_994_);
v___x_5059__boxed_1006_ = lean_unbox(v___x_995_);
v___x_5060__boxed_1007_ = lean_unbox(v___x_996_);
v_res_1008_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_5058__boxed_1005_, v___x_5059__boxed_1006_, v___x_5060__boxed_1007_, v_lctx_997_, v_init_998_, v_start_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v_start_999_);
return v_res_1008_;
}
}
lean_object* l_Lean_Meta_ppGoal___lam__0(uint8_t v___x_1012_, uint8_t v___x_1013_, uint8_t v___x_1014_, lean_object* v_fst_1015_, lean_object* v___x_1016_, lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_type_1019_, lean_object* v_val_1020_, lean_object* v_userName_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_1012_, v___x_1013_, v___x_1014_, v_fst_1015_, v___x_1016_, v___x_1017_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_snd_1029_; lean_object* v_fst_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1087_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_snd_1029_ = lean_ctor_get(v_a_1028_, 1);
v_fst_1030_ = lean_ctor_get(v_a_1028_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1032_ = v_a_1028_;
v_isShared_1033_ = v_isSharedCheck_1087_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1029_);
lean_inc(v_fst_1030_);
lean_dec(v_a_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1087_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1086_; 
v_fst_1034_ = lean_ctor_get(v_snd_1029_, 0);
v_snd_1035_ = lean_ctor_get(v_snd_1029_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_snd_1029_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1037_ = v_snd_1029_;
v_isShared_1038_ = v_isSharedCheck_1086_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_snd_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1086_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; 
lean_inc(v___x_1018_);
v___x_1039_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v___x_1018_, v_fst_1030_, v_fst_1034_, v_snd_1035_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1085_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1085_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1085_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1084_; 
v___x_1044_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_1040_);
v___x_1045_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1019_, v___y_1023_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1084_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1084_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Meta_ppExpr(v_a_1046_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1083_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1083_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1083_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = l_Lean_Meta_getGoalPrefix(v_val_1020_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 3);
lean_ctor_set(v___x_1048_, 0, v___x_1055_);
v___x_1057_ = v___x_1048_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 5);
lean_ctor_set(v___x_1037_, 1, v___x_1057_);
lean_ctor_set(v___x_1037_, 0, v___x_1044_);
v___x_1059_ = v___x_1037_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 4);
lean_ctor_set(v___x_1032_, 1, v_a_1051_);
lean_ctor_set(v___x_1032_, 0, v___x_1018_);
v___x_1061_ = v___x_1032_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1051_);
v___x_1061_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1059_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
if (lean_obj_tag(v_userName_1021_) == 0)
{
lean_object* v___x_1064_; 
lean_del_object(v___x_1042_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1062_);
v___x_1064_ = v___x_1053_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_ppGoal___lam__0___closed__1));
v___x_1067_ = l_Lean_Name_eraseMacroScopes(v_userName_1021_);
v___x_1068_ = 1;
v___x_1069_ = l_Lean_Name_toString(v___x_1067_, v___x_1068_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 3);
lean_ctor_set(v___x_1042_, 0, v___x_1069_);
v___x_1071_ = v___x_1042_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1066_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1062_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1075_);
v___x_1077_ = v___x_1053_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
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
lean_del_object(v___x_1048_);
lean_dec(v___x_1044_);
lean_del_object(v___x_1042_);
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec(v___x_1018_);
return v___x_1050_;
}
}
}
}
else
{
lean_del_object(v___x_1037_);
lean_del_object(v___x_1032_);
lean_dec_ref(v_type_1019_);
lean_dec(v___x_1018_);
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v_type_1019_);
lean_dec(v___x_1018_);
v_a_1088_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1027_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1027_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ppGoal___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1012_ = stack[0].m_num;
uint8_t v___x_1013_ = stack[1].m_num;
uint8_t v___x_1014_ = stack[2].m_num;
lean_object* v_fst_1015_ = stack[3].m_obj;
lean_object* v___x_1016_ = stack[4].m_obj;
lean_object* v___x_1017_ = stack[5].m_obj;
lean_object* v___x_1018_ = stack[6].m_obj;
lean_object* v_type_1019_ = stack[7].m_obj;
lean_object* v_val_1020_ = stack[8].m_obj;
lean_object* v_userName_1021_ = stack[9].m_obj;
lean_object* v___y_1022_ = stack[10].m_obj;
lean_object* v___y_1023_ = stack[11].m_obj;
lean_object* v___y_1024_ = stack[12].m_obj;
lean_object* v___y_1025_ = stack[13].m_obj;
lean_object* v_res_1096_;
v_res_1096_ = l_Lean_Meta_ppGoal___lam__0(v___x_1012_, v___x_1013_, v___x_1014_, v_fst_1015_, v___x_1016_, v___x_1017_, v___x_1018_, v_type_1019_, v_val_1020_, v_userName_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
stack->m_obj
 = v_res_1096_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_fst_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_type_1104_, lean_object* v_val_1105_, lean_object* v_userName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v___x_5110__boxed_1112_; uint8_t v___x_5111__boxed_1113_; uint8_t v___x_5112__boxed_1114_; lean_object* v_res_1115_; 
v___x_5110__boxed_1112_ = lean_unbox(v___x_1097_);
v___x_5111__boxed_1113_ = lean_unbox(v___x_1098_);
v___x_5112__boxed_1114_ = lean_unbox(v___x_1099_);
v_res_1115_ = l_Lean_Meta_ppGoal___lam__0(v___x_5110__boxed_1112_, v___x_5111__boxed_1113_, v___x_5112__boxed_1114_, v_fst_1100_, v___x_1101_, v___x_1102_, v___x_1103_, v_type_1104_, v_val_1105_, v_userName_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v_userName_1106_);
lean_dec_ref(v_val_1105_);
lean_dec(v___x_1102_);
return v_res_1115_;
}
}
lean_object* l_Lean_Meta_ppGoal(lean_object* v_mvarId_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_mctx_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_st_ref_get(v_a_1127_);
v_mctx_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_mctx_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1132_, v_mvarId_1125_);
lean_dec_ref(v_mctx_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__1));
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
else
{
lean_object* v_val_1136_; lean_object* v_userName_1137_; lean_object* v_lctx_1138_; lean_object* v_type_1139_; lean_object* v_localInstances_1140_; uint8_t v_kind_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; 
v_val_1136_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___x_1133_, 1);
v_userName_1137_ = lean_ctor_get(v_val_1136_, 0);
lean_inc(v_userName_1137_);
v_lctx_1138_ = lean_ctor_get(v_val_1136_, 1);
v_type_1139_ = lean_ctor_get(v_val_1136_, 2);
lean_inc_ref(v_type_1139_);
v_localInstances_1140_ = lean_ctor_get(v_val_1136_, 4);
lean_inc_ref(v_localInstances_1140_);
v_kind_1141_ = lean_ctor_get_uint8(v_val_1136_, sizeof(void*)*7);
v___x_1142_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1128_);
v___x_1143_ = l_Lean_Meta_pp_auxDecls;
v___x_1144_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v___x_1142_, v___x_1143_);
v___x_1145_ = l_Lean_Meta_pp_implementationDetailHyps;
v___x_1146_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v___x_1142_, v___x_1145_);
v___x_1147_ = lean_box(1);
v___x_1148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1142_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
lean_inc_ref(v_lctx_1138_);
v___x_1149_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1138_, v___x_1148_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_n(v_fst_1150_, 2);
lean_dec_ref(v___x_1149_);
v___x_1151_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
v___x_1152_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_1141_);
v___x_1153_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__3));
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_box(v___x_1146_);
v___x_1156_ = lean_box(v___x_1152_);
v___x_1157_ = lean_box(v___x_1144_);
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1158_, 0, v___x_1155_);
lean_closure_set(v___f_1158_, 1, v___x_1156_);
lean_closure_set(v___f_1158_, 2, v___x_1157_);
lean_closure_set(v___f_1158_, 3, v_fst_1150_);
lean_closure_set(v___f_1158_, 4, v___x_1153_);
lean_closure_set(v___f_1158_, 5, v___x_1154_);
lean_closure_set(v___f_1158_, 6, v___x_1151_);
lean_closure_set(v___f_1158_, 7, v_type_1139_);
lean_closure_set(v___f_1158_, 8, v_val_1136_);
lean_closure_set(v___f_1158_, 9, v_userName_1137_);
v___x_1159_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_fst_1150_, v_localInstances_1140_, v___f_1158_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1159_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ppGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1125_ = stack[0].m_obj;
lean_object* v_a_1126_ = stack[1].m_obj;
lean_object* v_a_1127_ = stack[2].m_obj;
lean_object* v_a_1128_ = stack[3].m_obj;
lean_object* v_a_1129_ = stack[4].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_Meta_ppGoal(v_mvarId_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object* v_mvarId_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Meta_ppGoal(v_mvarId_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_mvarId_1161_);
return v_res_1167_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_auxDecls = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_auxDecls);
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_implementationDetailHyps = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_implementationDetailHyps);
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_inaccessibleNames = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_inaccessibleNames);
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues);
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues_threshold);
lean_dec_ref(res);
res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues_tactic_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues_tactic_threshold);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_PPGoal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_PPGoal(builtin);
}
#ifdef __cplusplus
}
#endif
