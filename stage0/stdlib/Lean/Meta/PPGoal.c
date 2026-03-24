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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
uint8_t l_Lean_MetavarKind_isSyntheticOpaque(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "auxDecls"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 145, 51, 188, 89, 247, 104, 191)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "display auxiliary declarations used to compile recursive functions"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 146, 190, 114, 236, 223, 30, 15)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_auxDecls;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "implementationDetailHyps"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(95, 161, 54, 44, 105, 224, 181, 140)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "display implementation detail hypotheses in the local context"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(62, 255, 137, 94, 59, 236, 150, 82)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_implementationDetailHyps;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inaccessibleNames"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 160, 42, 6, 250, 122, 123, 232)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "display inaccessible declarations in the local context"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 204, 116, 106, 151, 53, 185, 129)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_inaccessibleNames;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showLetValues"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "always display let-declaration values in the info view"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 12, 21, 108, 66, 125, 244, 127)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 97, .m_data = "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 225, 32, 137, 29, 106, 114, 238)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues_threshold;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 8, 91, 225, 155, 186, 185, 50)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 21, 232, 108, 56, 195, 56, 160)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 235, 54, 94, 40, 62, 247, 246)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 115, .m_data = "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`, for tactic goals"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 39, 4, 70, 217, 113, 0, 124)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 190, 208, 67, 43, 188, 160, 41)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 176, 166, 194, 191, 152, 58, 125)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(22, 125, 62, 189, 243, 139, 141, 137)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_81_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_100_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_101_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_102_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_99_, v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_121_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_122_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_123_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_120_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(lean_object* v_name_126_, lean_object* v_decl_127_, lean_object* v_ref_128_){
_start:
{
lean_object* v_defValue_130_; lean_object* v_descr_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_157_; 
v_defValue_130_ = lean_ctor_get(v_decl_127_, 0);
v_descr_131_ = lean_ctor_get(v_decl_127_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_decl_127_);
if (v_isSharedCheck_157_ == 0)
{
v___x_133_ = v_decl_127_;
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_descr_131_);
lean_inc(v_defValue_130_);
lean_dec(v_decl_127_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_inc(v_defValue_130_);
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v_defValue_130_);
lean_inc(v_name_126_);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v_name_126_);
lean_ctor_set(v___x_136_, 1, v_ref_128_);
lean_ctor_set(v___x_136_, 2, v___x_135_);
lean_ctor_set(v___x_136_, 3, v_descr_131_);
lean_inc(v_name_126_);
v___x_137_ = lean_register_option(v_name_126_, v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_148_);
v___x_139_ = v___x_137_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_dec(v___x_137_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_defValue_130_);
lean_ctor_set(v___x_133_, 0, v_name_126_);
v___x_142_ = v___x_133_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_name_126_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_defValue_130_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_del_object(v___x_133_);
lean_dec(v_defValue_130_);
lean_dec(v_name_126_);
v_a_149_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_137_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_137_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_158_, lean_object* v_decl_159_, lean_object* v_ref_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v_name_158_, v_decl_159_, v_ref_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_180_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_181_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_182_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_179_, v___x_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_204_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_205_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_206_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_203_, v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
return v_res_208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(lean_object* v_opts_209_, lean_object* v_opt_210_){
_start:
{
lean_object* v_name_211_; lean_object* v_defValue_212_; lean_object* v_map_213_; lean_object* v___x_214_; 
v_name_211_ = lean_ctor_get(v_opt_210_, 0);
v_defValue_212_ = lean_ctor_get(v_opt_210_, 1);
v_map_213_ = lean_ctor_get(v_opts_209_, 0);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_213_, v_name_211_);
if (lean_obj_tag(v___x_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = lean_unbox(v_defValue_212_);
return v___x_215_;
}
else
{
lean_object* v_val_216_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v___x_214_);
if (lean_obj_tag(v_val_216_) == 1)
{
uint8_t v_v_217_; 
v_v_217_ = lean_ctor_get_uint8(v_val_216_, 0);
lean_dec_ref(v_val_216_);
return v_v_217_;
}
else
{
uint8_t v___x_218_; 
lean_dec(v_val_216_);
v___x_218_ = lean_unbox(v_defValue_212_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0___boxed(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_opts_219_, v_opt_220_);
lean_dec_ref(v_opt_220_);
lean_dec_ref(v_opts_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(lean_object* v_opts_223_, lean_object* v_opt_224_){
_start:
{
lean_object* v_name_225_; lean_object* v_defValue_226_; lean_object* v_map_227_; lean_object* v___x_228_; 
v_name_225_ = lean_ctor_get(v_opt_224_, 0);
v_defValue_226_ = lean_ctor_get(v_opt_224_, 1);
v_map_227_ = lean_ctor_get(v_opts_223_, 0);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_227_, v_name_225_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_inc(v_defValue_226_);
return v_defValue_226_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_229_);
lean_dec_ref(v___x_228_);
if (lean_obj_tag(v_val_229_) == 3)
{
lean_object* v_v_230_; 
v_v_230_ = lean_ctor_get(v_val_229_, 0);
lean_inc(v_v_230_);
lean_dec_ref(v_val_229_);
return v_v_230_;
}
else
{
lean_dec(v_val_229_);
lean_inc(v_defValue_226_);
return v_defValue_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1___boxed(lean_object* v_opts_231_, lean_object* v_opt_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_opts_231_, v_opt_232_);
lean_dec_ref(v_opt_232_);
lean_dec_ref(v_opts_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(uint8_t v_tactic_234_, lean_object* v_e_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___y_239_; lean_object* v___y_246_; uint8_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = l_Lean_Expr_isAtomic(v_e_235_);
v___x_250_ = 1;
if (v___x_249_ == 0)
{
lean_object* v_options_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_options_251_ = lean_ctor_get(v_a_236_, 2);
v___x_252_ = l_Lean_Meta_pp_showLetValues;
v___x_253_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___y_257_; 
v___x_254_ = l_Lean_Meta_pp_showLetValues_threshold;
v___x_255_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_251_, v___x_254_);
if (v_tactic_234_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___y_257_ = v___x_259_;
goto v___jp_256_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = l_Lean_Meta_pp_showLetValues_tactic_threshold;
v___x_261_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_251_, v___x_260_);
v___y_257_ = v___x_261_;
goto v___jp_256_;
}
v___jp_256_:
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_le(v___x_255_, v___y_257_);
if (v___x_258_ == 0)
{
lean_dec(v___y_257_);
v___y_246_ = v___x_255_;
goto v___jp_245_;
}
else
{
lean_dec(v___x_255_);
v___y_246_ = v___y_257_;
goto v___jp_245_;
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box(v___x_250_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_box(v___x_250_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
v___jp_238_:
{
uint32_t v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = l_Lean_Expr_approxDepth(v_e_235_);
v___x_241_ = lean_uint32_to_nat(v___x_240_);
v___x_242_ = lean_nat_dec_le(v___x_241_, v___y_239_);
lean_dec(v___y_239_);
lean_dec(v___x_241_);
v___x_243_ = lean_box(v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
v___jp_245_:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(254u);
v___x_248_ = lean_nat_dec_le(v___x_247_, v___y_246_);
if (v___x_248_ == 0)
{
v___y_239_ = v___y_246_;
goto v___jp_238_;
}
else
{
lean_dec(v___y_246_);
v___y_239_ = v___x_247_;
goto v___jp_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(lean_object* v_tactic_266_, lean_object* v_e_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
uint8_t v_tactic_boxed_270_; lean_object* v_res_271_; 
v_tactic_boxed_270_ = lean_unbox(v_tactic_266_);
v_res_271_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_boxed_270_, v_e_267_, v_a_268_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_e_267_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue(uint8_t v_tactic_272_, lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_272_, v_e_273_, v_a_276_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(lean_object* v_tactic_280_, lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
uint8_t v_tactic_boxed_287_; lean_object* v_res_288_; 
v_tactic_boxed_287_ = lean_unbox(v_tactic_280_);
v_res_288_ = l_Lean_Meta_ppGoal_shouldShowLetValue(v_tactic_boxed_287_, v_e_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_e_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object* v_fmt_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = l_Std_Format_isNil(v_fmt_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v_fmt_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
else
{
return v_fmt_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object* v_mvarDecl_298_){
_start:
{
lean_object* v_type_299_; lean_object* v___x_300_; 
v_type_299_ = lean_ctor_get(v_mvarDecl_298_, 2);
v___x_300_ = l_Lean_isLHSGoal_x3f(v_type_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__0));
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__1));
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object* v_mvarDecl_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_303_);
lean_dec_ref(v_mvarDecl_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_dec(v_x_305_);
return v_x_306_;
}
else
{
lean_object* v_head_308_; lean_object* v_tail_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_head_308_ = lean_ctor_get(v_x_307_, 0);
v_tail_309_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_x_307_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_tail_309_);
lean_inc(v_head_308_);
lean_dec(v_x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
lean_inc(v_x_305_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 5);
lean_ctor_set(v___x_311_, 1, v_x_305_);
lean_ctor_set(v___x_311_, 0, v_x_306_);
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_x_306_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_x_305_);
v___x_314_ = v_reuseFailAlloc_320_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = 1;
v___x_316_ = l_Lean_Name_toString(v_head_308_, v___x_315_);
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_314_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v_x_306_ = v___x_318_;
v_x_307_ = v_tail_309_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v___x_324_; 
lean_dec(v_x_323_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v_tail_325_; 
v_tail_325_ = lean_ctor_get(v_x_322_, 1);
if (lean_obj_tag(v_tail_325_) == 0)
{
lean_object* v_head_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_x_323_);
v_head_326_ = lean_ctor_get(v_x_322_, 0);
lean_inc(v_head_326_);
lean_dec_ref(v_x_322_);
v___x_327_ = 1;
v___x_328_ = l_Lean_Name_toString(v_head_326_, v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v_head_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_inc(v_tail_325_);
v_head_330_ = lean_ctor_get(v_x_322_, 0);
lean_inc(v_head_330_);
lean_dec_ref(v_x_322_);
v___x_331_ = 1;
v___x_332_ = l_Lean_Name_toString(v_head_330_, v___x_331_);
v___x_333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___x_334_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(v_x_323_, v___x_333_, v_tail_325_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(lean_object* v_indent_341_, lean_object* v_ids_342_, lean_object* v_type_x3f_343_, lean_object* v_fmt_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l_List_isEmpty___redArg(v_ids_342_);
if (v___x_350_ == 0)
{
lean_object* v_fmt_351_; 
v_fmt_351_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_fmt_344_);
if (lean_obj_tag(v_type_x3f_343_) == 0)
{
lean_object* v___x_352_; 
lean_dec(v_ids_342_);
lean_dec(v_indent_341_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_fmt_351_);
return v___x_352_;
}
else
{
lean_object* v_val_353_; lean_object* v___x_354_; 
v_val_353_ = lean_ctor_get(v_type_x3f_343_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v_type_x3f_343_);
v___x_354_ = l_Lean_Meta_ppExpr(v_val_353_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_374_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_374_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_374_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_374_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_359_ = l_List_reverse___redArg(v_ids_342_);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1));
v___x_361_ = l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(v___x_359_, v___x_360_);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3));
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_box(1);
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_355_);
v___x_366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_366_, 0, v_indent_341_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_363_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = 0;
v___x_369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_368_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v_fmt_351_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_370_);
v___x_372_ = v___x_357_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_dec(v_fmt_351_);
lean_dec(v_ids_342_);
lean_dec(v_indent_341_);
return v___x_354_;
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v_type_x3f_343_);
lean_dec(v_ids_342_);
lean_dec(v_indent_341_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_fmt_344_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(lean_object* v_indent_376_, lean_object* v_ids_377_, lean_object* v_type_x3f_378_, lean_object* v_fmt_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_376_, v_ids_377_, v_type_x3f_378_, v_fmt_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(lean_object* v_e_386_, lean_object* v___y_387_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_Expr_hasMVar(v_e_386_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_e_386_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v_mctx_392_; lean_object* v___x_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v___x_396_; lean_object* v_cache_397_; lean_object* v_zetaDeltaFVarIds_398_; lean_object* v_postponed_399_; lean_object* v_diag_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v___x_391_ = lean_st_ref_get(v___y_387_);
v_mctx_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc_ref(v_mctx_392_);
lean_dec(v___x_391_);
v___x_393_ = l_Lean_instantiateMVarsCore(v_mctx_392_, v_e_386_);
v_fst_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_snd_395_);
lean_dec_ref(v___x_393_);
v___x_396_ = lean_st_ref_take(v___y_387_);
v_cache_397_ = lean_ctor_get(v___x_396_, 1);
v_zetaDeltaFVarIds_398_ = lean_ctor_get(v___x_396_, 2);
v_postponed_399_ = lean_ctor_get(v___x_396_, 3);
v_diag_400_ = lean_ctor_get(v___x_396_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_410_);
v___x_402_ = v___x_396_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_diag_400_);
lean_inc(v_postponed_399_);
lean_inc(v_zetaDeltaFVarIds_398_);
lean_inc(v_cache_397_);
lean_dec(v___x_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_snd_395_);
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_snd_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_cache_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_400_);
v___x_405_ = v_reuseFailAlloc_408_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_st_ref_set(v___y_387_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_fst_394_);
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg___boxed(lean_object* v_e_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_411_, v___y_412_);
lean_dec(v___y_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(lean_object* v_e_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_415_, v___y_417_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object* v_e_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(v_e_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 1;
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
}
else
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 0;
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v_val_435_; uint8_t v___x_436_; 
v_val_434_ = lean_ctor_get(v_x_429_, 0);
v_val_435_ = lean_ctor_get(v_x_430_, 0);
v___x_436_ = lean_expr_eqv(v_val_434_, v_val_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_x_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec(v_x_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(lean_object* v_indent_450_, uint8_t v_tactic_451_, lean_object* v_varNames_452_, lean_object* v_prevType_x3f_453_, lean_object* v_fmt_454_, lean_object* v_localDecl_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
if (lean_obj_tag(v_localDecl_455_) == 0)
{
lean_object* v_userName_461_; lean_object* v_type_462_; lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_504_; 
v_userName_461_ = lean_ctor_get(v_localDecl_455_, 2);
lean_inc(v_userName_461_);
v_type_462_ = lean_ctor_get(v_localDecl_455_, 3);
lean_inc_ref(v_type_462_);
lean_dec_ref(v_localDecl_455_);
v___x_463_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_462_, v_a_457_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_504_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_504_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_504_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_varName_468_; uint8_t v___y_470_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_varName_468_ = lean_simp_macro_scopes(v_userName_461_);
v___x_500_ = lean_box(0);
v___x_501_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_453_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
lean_inc(v_a_464_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_a_464_);
v___x_503_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_453_, v___x_502_);
lean_dec_ref(v___x_502_);
v___y_470_ = v___x_503_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___x_501_;
goto v___jp_469_;
}
v___jp_469_:
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; 
lean_del_object(v___x_466_);
v___x_471_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_450_, v_varNames_452_, v_prevType_x3f_453_, v_fmt_454_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_484_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_484_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_varName_468_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_a_464_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_a_472_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_477_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_480_);
v___x_482_ = v___x_474_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_varName_468_);
lean_dec(v_a_464_);
v_a_485_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_471_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_471_);
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
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec(v_prevType_x3f_453_);
lean_dec(v_indent_450_);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v_varName_468_);
lean_ctor_set(v___x_493_, 1, v_varNames_452_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_a_464_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_fmt_454_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_496_);
v___x_498_ = v___x_466_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
else
{
uint8_t v_nondep_505_; 
v_nondep_505_ = lean_ctor_get_uint8(v_localDecl_455_, sizeof(void*)*5);
if (v_nondep_505_ == 0)
{
lean_object* v_userName_506_; lean_object* v_type_507_; lean_object* v_value_508_; lean_object* v___x_509_; 
v_userName_506_ = lean_ctor_get(v_localDecl_455_, 2);
lean_inc(v_userName_506_);
v_type_507_ = lean_ctor_get(v_localDecl_455_, 3);
lean_inc_ref(v_type_507_);
v_value_508_ = lean_ctor_get(v_localDecl_455_, 4);
lean_inc_ref(v_value_508_);
lean_dec_ref(v_localDecl_455_);
lean_inc(v_indent_450_);
v___x_509_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_450_, v_varNames_452_, v_prevType_x3f_453_, v_fmt_454_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_507_, v_a_457_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_Meta_ppExpr(v_a_512_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_567_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref(v___x_513_);
v___x_515_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_value_508_, v_a_457_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_567_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_567_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_567_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_566_; 
v___x_520_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_451_, v_a_516_, v_a_458_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_566_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_566_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_566_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_varName_525_; lean_object* v___x_526_; lean_object* v_fmtElem_528_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v_varName_525_ = lean_simp_macro_scopes(v_userName_506_);
v___x_526_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_510_);
v___x_539_ = 1;
v___x_540_ = l_Lean_Name_toString(v_varName_525_, v___x_539_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 3);
lean_ctor_set(v___x_518_, 0, v___x_540_);
v___x_542_ = v___x_518_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_565_;
goto v_reusejp_541_;
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
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_535_);
v___x_537_ = v___x_523_;
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
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1));
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_a_514_);
v___x_546_ = lean_unbox(v_a_521_);
lean_dec(v_a_521_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_a_516_);
lean_dec(v_indent_450_);
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3));
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_545_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v_fmtElem_528_ = v___x_548_;
goto v___jp_527_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_ppExpr(v_a_516_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5));
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_545_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_box(1);
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_a_550_);
v___x_555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_555_, 0, v_indent_450_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_552_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v_fmtElem_528_ = v___x_556_;
goto v___jp_527_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v___x_545_);
lean_dec(v___x_526_);
lean_del_object(v___x_523_);
lean_dec(v_indent_450_);
v_a_557_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_549_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_549_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
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
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_a_510_);
lean_dec_ref(v_value_508_);
lean_dec(v_userName_506_);
lean_dec(v_indent_450_);
v_a_568_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_513_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_513_);
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
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_value_508_);
lean_dec_ref(v_type_507_);
lean_dec(v_userName_506_);
lean_dec(v_indent_450_);
v_a_576_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_509_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_509_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_userName_584_; lean_object* v_type_585_; lean_object* v___x_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_627_; 
v_userName_584_ = lean_ctor_get(v_localDecl_455_, 2);
lean_inc(v_userName_584_);
v_type_585_ = lean_ctor_get(v_localDecl_455_, 3);
lean_inc_ref(v_type_585_);
lean_dec_ref(v_localDecl_455_);
v___x_586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_585_, v_a_457_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_627_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_627_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_627_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_varName_591_; uint8_t v___y_593_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_varName_591_ = lean_simp_macro_scopes(v_userName_584_);
v___x_623_ = lean_box(0);
v___x_624_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_453_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; 
lean_inc(v_a_587_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v_a_587_);
v___x_626_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_453_, v___x_625_);
lean_dec_ref(v___x_625_);
v___y_593_ = v___x_626_;
goto v___jp_592_;
}
else
{
v___y_593_ = v___x_624_;
goto v___jp_592_;
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; 
lean_del_object(v___x_589_);
v___x_594_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_450_, v_varNames_452_, v_prevType_x3f_453_, v_fmt_454_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_607_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_607_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_607_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_607_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v_varName_591_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_a_587_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v_a_595_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_603_);
v___x_605_ = v___x_597_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_varName_591_);
lean_dec(v_a_587_);
v_a_608_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_594_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_594_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v_prevType_x3f_453_);
lean_dec(v_indent_450_);
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v_varName_591_);
lean_ctor_set(v___x_616_, 1, v_varNames_452_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_a_587_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_fmt_454_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_616_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_619_);
v___x_621_ = v___x_589_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___boxed(lean_object* v_indent_628_, lean_object* v_tactic_629_, lean_object* v_varNames_630_, lean_object* v_prevType_x3f_631_, lean_object* v_fmt_632_, lean_object* v_localDecl_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
uint8_t v_tactic_boxed_639_; lean_object* v_res_640_; 
v_tactic_boxed_639_ = lean_unbox(v_tactic_629_);
v_res_640_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v_indent_628_, v_tactic_boxed_639_, v_varNames_630_, v_prevType_x3f_631_, v_fmt_632_, v_localDecl_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(lean_object* v_lctx_641_, lean_object* v_localInsts_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_641_, v_localInsts_642_, v_x_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_649_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_649_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg___boxed(lean_object* v_lctx_666_, lean_object* v_localInsts_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_666_, v_localInsts_667_, v_x_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(lean_object* v_00_u03b1_675_, lean_object* v_lctx_676_, lean_object* v_localInsts_677_, lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_676_, v_localInsts_677_, v_x_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___boxed(lean_object* v_00_u03b1_685_, lean_object* v_lctx_686_, lean_object* v_localInsts_687_, lean_object* v_x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(v_00_u03b1_685_, v_lctx_686_, v_localInsts_687_, v_x_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v_res_694_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(2u);
v___x_696_ = lean_nat_to_int(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(uint8_t v___x_697_, uint8_t v___x_698_, uint8_t v___x_699_, lean_object* v_as_700_, size_t v_i_701_, size_t v_stop_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_a_710_; lean_object* v___y_715_; uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_eq(v_i_701_, v_stop_702_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_array_uget_borrowed(v_as_700_, v_i_701_);
if (lean_obj_tag(v___x_718_) == 0)
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
else
{
lean_object* v_snd_719_; lean_object* v_val_720_; lean_object* v_fst_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_724_; 
v_snd_719_ = lean_ctor_get(v_b_703_, 1);
v_val_720_ = lean_ctor_get(v___x_718_, 0);
v_fst_721_ = lean_ctor_get(v_b_703_, 0);
v_fst_722_ = lean_ctor_get(v_snd_719_, 0);
v_snd_723_ = lean_ctor_get(v_snd_719_, 1);
v___x_724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
if (v___x_699_ == 0)
{
uint8_t v___x_729_; 
v___x_729_ = l_Lean_LocalDecl_isAuxDecl(v_val_720_);
if (v___x_729_ == 0)
{
goto v___jp_725_;
}
else
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
}
else
{
goto v___jp_725_;
}
v___jp_725_:
{
if (v___x_697_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_LocalDecl_isImplementationDetail(v_val_720_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_inc(v_snd_723_);
lean_inc(v_fst_722_);
lean_inc(v_fst_721_);
lean_dec_ref(v_b_703_);
lean_inc(v_val_720_);
v___x_727_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_724_, v___x_698_, v_fst_721_, v_fst_722_, v_snd_723_, v_val_720_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
v___y_715_ = v___x_727_;
goto v___jp_714_;
}
else
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
}
else
{
lean_object* v___x_728_; 
lean_inc(v_snd_723_);
lean_inc(v_fst_722_);
lean_inc(v_fst_721_);
lean_dec_ref(v_b_703_);
lean_inc(v_val_720_);
v___x_728_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_724_, v___x_698_, v_fst_721_, v_fst_722_, v_snd_723_, v_val_720_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
v___y_715_ = v___x_728_;
goto v___jp_714_;
}
}
}
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_703_);
return v___x_730_;
}
v___jp_709_:
{
size_t v___x_711_; size_t v___x_712_; 
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_701_, v___x_711_);
v_i_701_ = v___x_712_;
v_b_703_ = v_a_710_;
goto _start;
}
v___jp_714_:
{
if (lean_obj_tag(v___y_715_) == 0)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v___y_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref(v___y_715_);
v_a_710_ = v_a_716_;
goto v___jp_709_;
}
else
{
return v___y_715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v_as_734_, lean_object* v_i_735_, lean_object* v_stop_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v___x_5087__boxed_743_; uint8_t v___x_5088__boxed_744_; uint8_t v___x_5089__boxed_745_; size_t v_i_boxed_746_; size_t v_stop_boxed_747_; lean_object* v_res_748_; 
v___x_5087__boxed_743_ = lean_unbox(v___x_731_);
v___x_5088__boxed_744_ = lean_unbox(v___x_732_);
v___x_5089__boxed_745_ = lean_unbox(v___x_733_);
v_i_boxed_746_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_stop_boxed_747_ = lean_unbox_usize(v_stop_736_);
lean_dec(v_stop_736_);
v_res_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_5087__boxed_743_, v___x_5088__boxed_744_, v___x_5089__boxed_745_, v_as_734_, v_i_boxed_746_, v_stop_boxed_747_, v_b_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v_as_734_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(uint8_t v___x_749_, uint8_t v___x_750_, uint8_t v___x_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v_cs_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_779_; 
v_cs_759_ = lean_ctor_get(v_x_752_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_779_ == 0)
{
v___x_761_ = v_x_752_;
v_isShared_762_ = v_isSharedCheck_779_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_cs_759_);
lean_dec(v_x_752_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_779_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_array_get_size(v_cs_759_);
v___x_765_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v_cs_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_x_753_);
v___x_767_ = v___x_761_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_x_753_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_le(v___x_764_, v___x_764_);
if (v___x_769_ == 0)
{
if (v___x_765_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_cs_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_x_753_);
v___x_771_ = v___x_761_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_x_753_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_761_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_764_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_749_, v___x_750_, v___x_751_, v_cs_759_, v___x_773_, v___x_774_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_cs_759_);
return v___x_775_;
}
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_del_object(v___x_761_);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_of_nat(v___x_764_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_749_, v___x_750_, v___x_751_, v_cs_759_, v___x_776_, v___x_777_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_cs_759_);
return v___x_778_;
}
}
}
}
else
{
lean_object* v_vs_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_800_; 
v_vs_780_ = lean_ctor_get(v_x_752_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_800_ == 0)
{
v___x_782_ = v_x_752_;
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_vs_780_);
lean_dec(v_x_752_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_800_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_array_get_size(v_vs_780_);
v___x_786_ = lean_nat_dec_lt(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_vs_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 0);
lean_ctor_set(v___x_782_, 0, v_x_753_);
v___x_788_ = v___x_782_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_x_753_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_785_, v___x_785_);
if (v___x_790_ == 0)
{
if (v___x_786_ == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v_vs_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 0);
lean_ctor_set(v___x_782_, 0, v_x_753_);
v___x_792_ = v___x_782_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_x_753_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_782_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_of_nat(v___x_785_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_749_, v___x_750_, v___x_751_, v_vs_780_, v___x_794_, v___x_795_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_vs_780_);
return v___x_796_;
}
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_782_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_of_nat(v___x_785_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_749_, v___x_750_, v___x_751_, v_vs_780_, v___x_797_, v___x_798_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_vs_780_);
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(uint8_t v___x_801_, uint8_t v___x_802_, uint8_t v___x_803_, lean_object* v_as_804_, size_t v_i_805_, size_t v_stop_806_, lean_object* v_b_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = lean_usize_dec_eq(v_i_805_, v_stop_806_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_array_uget_borrowed(v_as_804_, v_i_805_);
lean_inc(v___x_814_);
v___x_815_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_801_, v___x_802_, v___x_803_, v___x_814_, v_b_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; size_t v___x_817_; size_t v___x_818_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_805_, v___x_817_);
v_i_805_ = v___x_818_;
v_b_807_ = v_a_816_;
goto _start;
}
else
{
return v___x_815_;
}
}
else
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_807_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v_as_824_, lean_object* v_i_825_, lean_object* v_stop_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v___x_5158__boxed_833_; uint8_t v___x_5159__boxed_834_; uint8_t v___x_5160__boxed_835_; size_t v_i_boxed_836_; size_t v_stop_boxed_837_; lean_object* v_res_838_; 
v___x_5158__boxed_833_ = lean_unbox(v___x_821_);
v___x_5159__boxed_834_ = lean_unbox(v___x_822_);
v___x_5160__boxed_835_ = lean_unbox(v___x_823_);
v_i_boxed_836_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_stop_boxed_837_ = lean_unbox_usize(v_stop_826_);
lean_dec(v_stop_826_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_5158__boxed_833_, v___x_5159__boxed_834_, v___x_5160__boxed_835_, v_as_824_, v_i_boxed_836_, v_stop_boxed_837_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v_as_824_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___x_5175__boxed_849_; uint8_t v___x_5176__boxed_850_; uint8_t v___x_5177__boxed_851_; lean_object* v_res_852_; 
v___x_5175__boxed_849_ = lean_unbox(v___x_839_);
v___x_5176__boxed_850_ = lean_unbox(v___x_840_);
v___x_5177__boxed_851_ = lean_unbox(v___x_841_);
v_res_852_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_5175__boxed_849_, v___x_5176__boxed_850_, v___x_5177__boxed_851_, v_x_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_852_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(uint8_t v___x_854_, uint8_t v___x_855_, uint8_t v___x_856_, lean_object* v_x_857_, size_t v_x_858_, size_t v_x_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_object* v_cs_866_; lean_object* v___x_867_; size_t v___x_868_; lean_object* v_j_869_; lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v_cs_866_ = lean_ctor_get(v_x_857_, 0);
lean_inc_ref(v_cs_866_);
lean_dec_ref(v_x_857_);
v___x_867_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0);
v___x_868_ = lean_usize_shift_right(v_x_858_, v_x_859_);
v_j_869_ = lean_usize_to_nat(v___x_868_);
v___x_870_ = lean_array_get_borrowed(v___x_867_, v_cs_866_, v_j_869_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_shift_left(v___x_871_, v_x_859_);
v___x_873_ = lean_usize_sub(v___x_872_, v___x_871_);
v___x_874_ = lean_usize_land(v_x_858_, v___x_873_);
v___x_875_ = ((size_t)5ULL);
v___x_876_ = lean_usize_sub(v_x_859_, v___x_875_);
lean_inc(v___x_870_);
v___x_877_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_854_, v___x_855_, v___x_856_, v___x_870_, v___x_874_, v___x_876_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_j_869_, v___x_879_);
lean_dec(v_j_869_);
v___x_881_ = lean_array_get_size(v_cs_866_);
v___x_882_ = lean_nat_dec_lt(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_dec(v___x_880_);
lean_dec(v_a_878_);
lean_dec_ref(v_cs_866_);
return v___x_877_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = lean_nat_dec_le(v___x_881_, v___x_881_);
if (v___x_883_ == 0)
{
if (v___x_882_ == 0)
{
lean_dec(v___x_880_);
lean_dec(v_a_878_);
lean_dec_ref(v_cs_866_);
return v___x_877_;
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v___x_877_);
v___x_884_ = lean_usize_of_nat(v___x_880_);
lean_dec(v___x_880_);
v___x_885_ = lean_usize_of_nat(v___x_881_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_854_, v___x_855_, v___x_856_, v_cs_866_, v___x_884_, v___x_885_, v_a_878_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec_ref(v_cs_866_);
return v___x_886_;
}
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v___x_877_);
v___x_887_ = lean_usize_of_nat(v___x_880_);
lean_dec(v___x_880_);
v___x_888_ = lean_usize_of_nat(v___x_881_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_854_, v___x_855_, v___x_856_, v_cs_866_, v___x_887_, v___x_888_, v_a_878_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec_ref(v_cs_866_);
return v___x_889_;
}
}
}
else
{
lean_dec(v_j_869_);
lean_dec_ref(v_cs_866_);
return v___x_877_;
}
}
else
{
lean_object* v_vs_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_910_; 
v_vs_890_ = lean_ctor_get(v_x_857_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_910_ == 0)
{
v___x_892_ = v_x_857_;
v_isShared_893_ = v_isSharedCheck_910_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_vs_890_);
lean_dec(v_x_857_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_910_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = lean_usize_to_nat(v_x_858_);
v___x_895_ = lean_array_get_size(v_vs_890_);
v___x_896_ = lean_nat_dec_lt(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v___x_894_);
lean_dec_ref(v_vs_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v_x_860_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_x_860_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
uint8_t v___x_900_; 
v___x_900_ = lean_nat_dec_le(v___x_895_, v___x_895_);
if (v___x_900_ == 0)
{
if (v___x_896_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v___x_894_);
lean_dec_ref(v_vs_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v_x_860_);
v___x_902_ = v___x_892_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_x_860_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
lean_del_object(v___x_892_);
v___x_904_ = lean_usize_of_nat(v___x_894_);
lean_dec(v___x_894_);
v___x_905_ = lean_usize_of_nat(v___x_895_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_854_, v___x_855_, v___x_856_, v_vs_890_, v___x_904_, v___x_905_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec_ref(v_vs_890_);
return v___x_906_;
}
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
lean_del_object(v___x_892_);
v___x_907_ = lean_usize_of_nat(v___x_894_);
lean_dec(v___x_894_);
v___x_908_ = lean_usize_of_nat(v___x_895_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_854_, v___x_855_, v___x_856_, v_vs_890_, v___x_907_, v___x_908_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec_ref(v_vs_890_);
return v___x_909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v___x_5315__boxed_923_; uint8_t v___x_5316__boxed_924_; uint8_t v___x_5317__boxed_925_; size_t v_x_5319__boxed_926_; size_t v_x_5320__boxed_927_; lean_object* v_res_928_; 
v___x_5315__boxed_923_ = lean_unbox(v___x_911_);
v___x_5316__boxed_924_ = lean_unbox(v___x_912_);
v___x_5317__boxed_925_ = lean_unbox(v___x_913_);
v_x_5319__boxed_926_ = lean_unbox_usize(v_x_915_);
lean_dec(v_x_915_);
v_x_5320__boxed_927_ = lean_unbox_usize(v_x_916_);
lean_dec(v_x_916_);
v_res_928_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_5315__boxed_923_, v___x_5316__boxed_924_, v___x_5317__boxed_925_, v_x_914_, v_x_5319__boxed_926_, v_x_5320__boxed_927_, v_x_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(uint8_t v___x_929_, uint8_t v___x_930_, uint8_t v___x_931_, lean_object* v_t_932_, lean_object* v_init_933_, lean_object* v_start_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_nat_dec_eq(v_start_934_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v_root_942_; lean_object* v_tail_943_; size_t v_shift_944_; lean_object* v_tailOff_945_; uint8_t v___x_946_; 
v_root_942_ = lean_ctor_get(v_t_932_, 0);
lean_inc_ref(v_root_942_);
v_tail_943_ = lean_ctor_get(v_t_932_, 1);
lean_inc_ref(v_tail_943_);
v_shift_944_ = lean_ctor_get_usize(v_t_932_, 4);
v_tailOff_945_ = lean_ctor_get(v_t_932_, 3);
lean_inc(v_tailOff_945_);
lean_dec_ref(v_t_932_);
v___x_946_ = lean_nat_dec_le(v_tailOff_945_, v_start_934_);
if (v___x_946_ == 0)
{
size_t v___x_947_; lean_object* v___x_948_; 
lean_dec(v_tailOff_945_);
v___x_947_ = lean_usize_of_nat(v_start_934_);
v___x_948_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_929_, v___x_930_, v___x_931_, v_root_942_, v___x_947_, v_shift_944_, v_init_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
v___x_950_ = lean_array_get_size(v_tail_943_);
v___x_951_ = lean_nat_dec_lt(v___x_940_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec(v_a_949_);
lean_dec_ref(v_tail_943_);
return v___x_948_;
}
else
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_le(v___x_950_, v___x_950_);
if (v___x_952_ == 0)
{
if (v___x_951_ == 0)
{
lean_dec(v_a_949_);
lean_dec_ref(v_tail_943_);
return v___x_948_;
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_dec_ref(v___x_948_);
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_950_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_943_, v___x_953_, v___x_954_, v_a_949_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_943_);
return v___x_955_;
}
}
else
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v___x_948_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_950_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_943_, v___x_956_, v___x_957_, v_a_949_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_943_);
return v___x_958_;
}
}
}
else
{
lean_dec_ref(v_tail_943_);
return v___x_948_;
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
lean_dec_ref(v_root_942_);
v___x_959_ = lean_nat_sub(v_start_934_, v_tailOff_945_);
lean_dec(v_tailOff_945_);
v___x_960_ = lean_array_get_size(v_tail_943_);
v___x_961_ = lean_nat_dec_lt(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v___x_959_);
lean_dec_ref(v_tail_943_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_init_933_);
return v___x_962_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_le(v___x_960_, v___x_960_);
if (v___x_963_ == 0)
{
if (v___x_961_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v___x_959_);
lean_dec_ref(v_tail_943_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_init_933_);
return v___x_964_;
}
else
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_usize_of_nat(v___x_959_);
lean_dec(v___x_959_);
v___x_966_ = lean_usize_of_nat(v___x_960_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_943_, v___x_965_, v___x_966_, v_init_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_943_);
return v___x_967_;
}
}
else
{
size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_usize_of_nat(v___x_959_);
lean_dec(v___x_959_);
v___x_969_ = lean_usize_of_nat(v___x_960_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_943_, v___x_968_, v___x_969_, v_init_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_943_);
return v___x_970_;
}
}
}
}
else
{
lean_object* v_root_971_; lean_object* v_tail_972_; lean_object* v___x_973_; 
v_root_971_ = lean_ctor_get(v_t_932_, 0);
lean_inc_ref(v_root_971_);
v_tail_972_ = lean_ctor_get(v_t_932_, 1);
lean_inc_ref(v_tail_972_);
lean_dec_ref(v_t_932_);
v___x_973_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_929_, v___x_930_, v___x_931_, v_root_971_, v_init_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
v___x_975_ = lean_array_get_size(v_tail_972_);
v___x_976_ = lean_nat_dec_lt(v___x_940_, v___x_975_);
if (v___x_976_ == 0)
{
lean_dec(v_a_974_);
lean_dec_ref(v_tail_972_);
return v___x_973_;
}
else
{
uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_le(v___x_975_, v___x_975_);
if (v___x_977_ == 0)
{
if (v___x_976_ == 0)
{
lean_dec(v_a_974_);
lean_dec_ref(v_tail_972_);
return v___x_973_;
}
else
{
size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v___x_973_);
v___x_978_ = ((size_t)0ULL);
v___x_979_ = lean_usize_of_nat(v___x_975_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_972_, v___x_978_, v___x_979_, v_a_974_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_972_);
return v___x_980_;
}
}
else
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
lean_dec_ref(v___x_973_);
v___x_981_ = ((size_t)0ULL);
v___x_982_ = lean_usize_of_nat(v___x_975_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_929_, v___x_930_, v___x_931_, v_tail_972_, v___x_981_, v___x_982_, v_a_974_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v_tail_972_);
return v___x_983_;
}
}
}
else
{
lean_dec_ref(v_tail_972_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v_t_987_, lean_object* v_init_988_, lean_object* v_start_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_5441__boxed_995_; uint8_t v___x_5442__boxed_996_; uint8_t v___x_5443__boxed_997_; lean_object* v_res_998_; 
v___x_5441__boxed_995_ = lean_unbox(v___x_984_);
v___x_5442__boxed_996_ = lean_unbox(v___x_985_);
v___x_5443__boxed_997_ = lean_unbox(v___x_986_);
v_res_998_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_5441__boxed_995_, v___x_5442__boxed_996_, v___x_5443__boxed_997_, v_t_987_, v_init_988_, v_start_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v_start_989_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(uint8_t v___x_999_, uint8_t v___x_1000_, uint8_t v___x_1001_, lean_object* v_lctx_1002_, lean_object* v_init_1003_, lean_object* v_start_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_decls_1010_; lean_object* v___x_1011_; 
v_decls_1010_ = lean_ctor_get(v_lctx_1002_, 1);
lean_inc_ref(v_decls_1010_);
lean_dec_ref(v_lctx_1002_);
v___x_1011_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_999_, v___x_1000_, v___x_1001_, v_decls_1010_, v_init_1003_, v_start_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v___x_1014_, lean_object* v_lctx_1015_, lean_object* v_init_1016_, lean_object* v_start_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_5543__boxed_1023_; uint8_t v___x_5544__boxed_1024_; uint8_t v___x_5545__boxed_1025_; lean_object* v_res_1026_; 
v___x_5543__boxed_1023_ = lean_unbox(v___x_1012_);
v___x_5544__boxed_1024_ = lean_unbox(v___x_1013_);
v___x_5545__boxed_1025_ = lean_unbox(v___x_1014_);
v_res_1026_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_5543__boxed_1023_, v___x_5544__boxed_1024_, v___x_5545__boxed_1025_, v_lctx_1015_, v_init_1016_, v_start_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_start_1017_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(uint8_t v___x_1030_, uint8_t v___x_1031_, uint8_t v___x_1032_, lean_object* v_fst_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_type_1037_, lean_object* v_val_1038_, lean_object* v_userName_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_1030_, v___x_1031_, v___x_1032_, v_fst_1033_, v___x_1034_, v___x_1035_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_snd_1047_; lean_object* v_fst_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1105_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v_snd_1047_ = lean_ctor_get(v_a_1046_, 1);
v_fst_1048_ = lean_ctor_get(v_a_1046_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1046_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1050_ = v_a_1046_;
v_isShared_1051_ = v_isSharedCheck_1105_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1047_);
lean_inc(v_fst_1048_);
lean_dec(v_a_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1105_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1104_; 
v_fst_1052_ = lean_ctor_get(v_snd_1047_, 0);
v_snd_1053_ = lean_ctor_get(v_snd_1047_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_snd_1047_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1055_ = v_snd_1047_;
v_isShared_1056_ = v_isSharedCheck_1104_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v_snd_1047_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1104_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; 
lean_inc(v___x_1036_);
v___x_1057_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v___x_1036_, v_fst_1048_, v_fst_1052_, v_snd_1053_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1103_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1103_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1103_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1102_; 
v___x_1062_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1037_, v___y_1041_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1102_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1102_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_ppExpr(v_a_1063_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1101_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1101_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1101_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1072_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_1058_);
v___x_1073_ = l_Lean_Meta_getGoalPrefix(v_val_1038_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 3);
lean_ctor_set(v___x_1065_, 0, v___x_1073_);
v___x_1075_ = v___x_1065_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 5);
lean_ctor_set(v___x_1055_, 1, v___x_1075_);
lean_ctor_set(v___x_1055_, 0, v___x_1072_);
v___x_1077_ = v___x_1055_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 4);
lean_ctor_set(v___x_1050_, 1, v_a_1068_);
lean_ctor_set(v___x_1050_, 0, v___x_1036_);
v___x_1079_ = v___x_1050_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_a_1068_);
v___x_1079_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
if (lean_obj_tag(v_userName_1039_) == 0)
{
lean_object* v___x_1082_; 
lean_del_object(v___x_1060_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1080_);
v___x_1082_ = v___x_1070_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1084_ = ((lean_object*)(l_Lean_Meta_ppGoal___lam__0___closed__1));
v___x_1085_ = lean_erase_macro_scopes(v_userName_1039_);
v___x_1086_ = 1;
v___x_1087_ = l_Lean_Name_toString(v___x_1085_, v___x_1086_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 3);
lean_ctor_set(v___x_1060_, 0, v___x_1087_);
v___x_1089_ = v___x_1060_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1084_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1080_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1093_);
v___x_1095_ = v___x_1070_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
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
lean_del_object(v___x_1065_);
lean_del_object(v___x_1060_);
lean_dec(v_a_1058_);
lean_del_object(v___x_1055_);
lean_del_object(v___x_1050_);
lean_dec(v_userName_1039_);
lean_dec(v___x_1036_);
return v___x_1067_;
}
}
}
}
else
{
lean_del_object(v___x_1055_);
lean_del_object(v___x_1050_);
lean_dec(v_userName_1039_);
lean_dec_ref(v_type_1037_);
lean_dec(v___x_1036_);
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v_userName_1039_);
lean_dec_ref(v_type_1037_);
lean_dec(v___x_1036_);
v_a_1106_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1045_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1045_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object* v___x_1114_, lean_object* v___x_1115_, lean_object* v___x_1116_, lean_object* v_fst_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v_type_1121_, lean_object* v_val_1122_, lean_object* v_userName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v___x_5578__boxed_1129_; uint8_t v___x_5579__boxed_1130_; uint8_t v___x_5580__boxed_1131_; lean_object* v_res_1132_; 
v___x_5578__boxed_1129_ = lean_unbox(v___x_1114_);
v___x_5579__boxed_1130_ = lean_unbox(v___x_1115_);
v___x_5580__boxed_1131_ = lean_unbox(v___x_1116_);
v_res_1132_ = l_Lean_Meta_ppGoal___lam__0(v___x_5578__boxed_1129_, v___x_5579__boxed_1130_, v___x_5580__boxed_1131_, v_fst_1117_, v___x_1118_, v___x_1119_, v___x_1120_, v_type_1121_, v_val_1122_, v_userName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_val_1122_);
lean_dec(v___x_1119_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object* v_mvarId_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v_mctx_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_st_ref_get(v_a_1144_);
v_mctx_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_mctx_1149_);
lean_dec(v___x_1148_);
v___x_1150_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1149_, v_mvarId_1142_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
v___x_1151_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__1));
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; lean_object* v_options_1154_; lean_object* v_userName_1155_; lean_object* v_lctx_1156_; lean_object* v_type_1157_; lean_object* v_localInstances_1158_; uint8_t v_kind_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v_val_1153_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1153_);
lean_dec_ref(v___x_1150_);
v_options_1154_ = lean_ctor_get(v_a_1145_, 2);
v_userName_1155_ = lean_ctor_get(v_val_1153_, 0);
lean_inc(v_userName_1155_);
v_lctx_1156_ = lean_ctor_get(v_val_1153_, 1);
v_type_1157_ = lean_ctor_get(v_val_1153_, 2);
lean_inc_ref(v_type_1157_);
v_localInstances_1158_ = lean_ctor_get(v_val_1153_, 4);
lean_inc_ref(v_localInstances_1158_);
v_kind_1159_ = lean_ctor_get_uint8(v_val_1153_, sizeof(void*)*7);
v___x_1160_ = l_Lean_Meta_pp_auxDecls;
v___x_1161_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1154_, v___x_1160_);
v___x_1162_ = l_Lean_Meta_pp_implementationDetailHyps;
v___x_1163_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1154_, v___x_1162_);
v___x_1164_ = lean_box(1);
lean_inc_ref(v_options_1154_);
v___x_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1165_, 0, v_options_1154_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
lean_inc_ref(v_lctx_1156_);
v___x_1166_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1156_, v___x_1165_);
v_fst_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_fst_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
v___x_1169_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_1159_);
v___x_1170_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__3));
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_box(v___x_1163_);
v___x_1173_ = lean_box(v___x_1169_);
v___x_1174_ = lean_box(v___x_1161_);
lean_inc(v_fst_1167_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1175_, 0, v___x_1172_);
lean_closure_set(v___f_1175_, 1, v___x_1173_);
lean_closure_set(v___f_1175_, 2, v___x_1174_);
lean_closure_set(v___f_1175_, 3, v_fst_1167_);
lean_closure_set(v___f_1175_, 4, v___x_1170_);
lean_closure_set(v___f_1175_, 5, v___x_1171_);
lean_closure_set(v___f_1175_, 6, v___x_1168_);
lean_closure_set(v___f_1175_, 7, v_type_1157_);
lean_closure_set(v___f_1175_, 8, v_val_1153_);
lean_closure_set(v___f_1175_, 9, v_userName_1155_);
v___x_1176_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_fst_1167_, v_localInstances_1158_, v___f_1175_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object* v_mvarId_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_ppGoal(v_mvarId_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_mvarId_1177_);
return v_res_1183_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_auxDecls = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_auxDecls);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_implementationDetailHyps = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_implementationDetailHyps);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_inaccessibleNames = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_inaccessibleNames);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues_threshold);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
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
