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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_simpMacroScopes(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_));
v___x_78_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_75_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_));
v___x_100_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_97_, v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_));
v___x_122_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_119_, v___x_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(lean_object* v_name_125_, lean_object* v_decl_126_, lean_object* v_ref_127_){
_start:
{
lean_object* v_defValue_129_; lean_object* v_descr_130_; lean_object* v_deprecation_x3f_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_defValue_129_ = lean_ctor_get(v_decl_126_, 0);
v_descr_130_ = lean_ctor_get(v_decl_126_, 1);
v_deprecation_x3f_131_ = lean_ctor_get(v_decl_126_, 2);
lean_inc(v_defValue_129_);
v___x_132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_132_, 0, v_defValue_129_);
lean_inc(v_deprecation_x3f_131_);
lean_inc_ref(v_descr_130_);
lean_inc_n(v_name_125_, 2);
v___x_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_133_, 0, v_name_125_);
lean_ctor_set(v___x_133_, 1, v_ref_127_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
lean_ctor_set(v___x_133_, 3, v_descr_130_);
lean_ctor_set(v___x_133_, 4, v_deprecation_x3f_131_);
v___x_134_ = lean_register_option(v_name_125_, v___x_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_143_);
v___x_136_ = v___x_134_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_dec(v___x_134_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_inc(v_defValue_129_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_name_125_);
lean_ctor_set(v___x_138_, 1, v_defValue_129_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_name_125_);
v_a_144_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_134_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_134_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_152_, lean_object* v_decl_153_, lean_object* v_ref_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v_name_152_, v_decl_153_, v_ref_154_);
lean_dec_ref(v_decl_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_));
v___x_177_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_174_, v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_));
v___x_202_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(lean_object* v_opts_205_, lean_object* v_opt_206_){
_start:
{
lean_object* v_name_207_; lean_object* v_defValue_208_; lean_object* v_map_209_; lean_object* v___x_210_; 
v_name_207_ = lean_ctor_get(v_opt_206_, 0);
v_defValue_208_ = lean_ctor_get(v_opt_206_, 1);
v_map_209_ = lean_ctor_get(v_opts_205_, 0);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_209_, v_name_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = lean_unbox(v_defValue_208_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
if (lean_obj_tag(v_val_212_) == 1)
{
uint8_t v_v_213_; 
v_v_213_ = lean_ctor_get_uint8(v_val_212_, 0);
lean_dec_ref_known(v_val_212_, 0);
return v_v_213_;
}
else
{
uint8_t v___x_214_; 
lean_dec(v_val_212_);
v___x_214_ = lean_unbox(v_defValue_208_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0___boxed(lean_object* v_opts_215_, lean_object* v_opt_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_opts_215_, v_opt_216_);
lean_dec_ref(v_opt_216_);
lean_dec_ref(v_opts_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
lean_object* v_name_221_; lean_object* v_defValue_222_; lean_object* v_map_223_; lean_object* v___x_224_; 
v_name_221_ = lean_ctor_get(v_opt_220_, 0);
v_defValue_222_ = lean_ctor_get(v_opt_220_, 1);
v_map_223_ = lean_ctor_get(v_opts_219_, 0);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_223_, v_name_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_inc(v_defValue_222_);
return v_defValue_222_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
if (lean_obj_tag(v_val_225_) == 3)
{
lean_object* v_v_226_; 
v_v_226_ = lean_ctor_get(v_val_225_, 0);
lean_inc(v_v_226_);
lean_dec_ref_known(v_val_225_, 1);
return v_v_226_;
}
else
{
lean_dec(v_val_225_);
lean_inc(v_defValue_222_);
return v_defValue_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1___boxed(lean_object* v_opts_227_, lean_object* v_opt_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_opts_227_, v_opt_228_);
lean_dec_ref(v_opt_228_);
lean_dec_ref(v_opts_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(uint8_t v_tactic_230_, lean_object* v_e_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___y_235_; lean_object* v___y_242_; uint8_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = l_Lean_Expr_isAtomic(v_e_231_);
v___x_246_ = 1;
if (v___x_245_ == 0)
{
lean_object* v_toCold_247_; lean_object* v_options_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_toCold_247_ = lean_ctor_get(v_a_232_, 0);
v_options_248_ = lean_ctor_get(v_toCold_247_, 2);
v___x_249_ = l_Lean_Meta_pp_showLetValues;
v___x_250_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___y_254_; 
v___x_251_ = l_Lean_Meta_pp_showLetValues_threshold;
v___x_252_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_248_, v___x_251_);
if (v_tactic_230_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___y_254_ = v___x_256_;
goto v___jp_253_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = l_Lean_Meta_pp_showLetValues_tactic_threshold;
v___x_258_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_248_, v___x_257_);
v___y_254_ = v___x_258_;
goto v___jp_253_;
}
v___jp_253_:
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_le(v___x_252_, v___y_254_);
if (v___x_255_ == 0)
{
lean_dec(v___y_254_);
v___y_242_ = v___x_252_;
goto v___jp_241_;
}
else
{
lean_dec(v___x_252_);
v___y_242_ = v___y_254_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(v___x_246_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(v___x_246_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
v___jp_234_:
{
uint32_t v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_236_ = l_Lean_Expr_approxDepth(v_e_231_);
v___x_237_ = lean_uint32_to_nat(v___x_236_);
v___x_238_ = lean_nat_dec_le(v___x_237_, v___y_235_);
lean_dec(v___y_235_);
lean_dec(v___x_237_);
v___x_239_ = lean_box(v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
v___jp_241_:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(254u);
v___x_244_ = lean_nat_dec_le(v___x_243_, v___y_242_);
if (v___x_244_ == 0)
{
v___y_235_ = v___y_242_;
goto v___jp_234_;
}
else
{
lean_dec(v___y_242_);
v___y_235_ = v___x_243_;
goto v___jp_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(lean_object* v_tactic_263_, lean_object* v_e_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
uint8_t v_tactic_boxed_267_; lean_object* v_res_268_; 
v_tactic_boxed_267_ = lean_unbox(v_tactic_263_);
v_res_268_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_boxed_267_, v_e_264_, v_a_265_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_e_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue(uint8_t v_tactic_269_, lean_object* v_e_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_269_, v_e_270_, v_a_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(lean_object* v_tactic_277_, lean_object* v_e_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
uint8_t v_tactic_boxed_284_; lean_object* v_res_285_; 
v_tactic_boxed_284_ = lean_unbox(v_tactic_277_);
v_res_285_ = l_Lean_Meta_ppGoal_shouldShowLetValue(v_tactic_boxed_284_, v_e_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec_ref(v_e_278_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object* v_fmt_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Std_Format_isNil(v_fmt_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v_fmt_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
else
{
return v_fmt_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object* v_mvarDecl_295_){
_start:
{
lean_object* v_type_296_; lean_object* v___x_297_; 
v_type_296_ = lean_ctor_get(v_mvarDecl_295_, 2);
v___x_297_ = l_Lean_isLHSGoal_x3f(v_type_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__0));
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__1));
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object* v_mvarDecl_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_300_);
lean_dec_ref(v_mvarDecl_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_dec(v_x_302_);
return v_x_303_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_318_; 
v_head_305_ = lean_ctor_get(v_x_304_, 0);
v_tail_306_ = lean_ctor_get(v_x_304_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_318_ == 0)
{
v___x_308_ = v_x_304_;
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_tail_306_);
lean_inc(v_head_305_);
lean_dec(v_x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
lean_inc(v_x_302_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 5);
lean_ctor_set(v___x_308_, 1, v_x_302_);
lean_ctor_set(v___x_308_, 0, v_x_303_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_303_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_x_302_);
v___x_311_ = v_reuseFailAlloc_317_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = 1;
v___x_313_ = l_Lean_Name_toString(v_head_305_, v___x_312_);
v___x_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_311_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v_x_303_ = v___x_315_;
v_x_304_ = v_tail_306_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v___x_321_; 
lean_dec(v_x_320_);
v___x_321_ = lean_box(0);
return v___x_321_;
}
else
{
lean_object* v_tail_322_; 
v_tail_322_ = lean_ctor_get(v_x_319_, 1);
if (lean_obj_tag(v_tail_322_) == 0)
{
lean_object* v_head_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_x_320_);
v_head_323_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_head_323_);
lean_dec_ref_known(v_x_319_, 2);
v___x_324_ = 1;
v___x_325_ = l_Lean_Name_toString(v_head_323_, v___x_324_);
v___x_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v_head_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_inc(v_tail_322_);
v_head_327_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_head_327_);
lean_dec_ref_known(v_x_319_, 2);
v___x_328_ = 1;
v___x_329_ = l_Lean_Name_toString(v_head_327_, v___x_328_);
v___x_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(v_x_320_, v___x_330_, v_tail_322_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(lean_object* v_indent_338_, lean_object* v_ids_339_, lean_object* v_type_x3f_340_, lean_object* v_fmt_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_List_isEmpty___redArg(v_ids_339_);
if (v___x_347_ == 0)
{
lean_object* v_fmt_348_; 
v_fmt_348_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_fmt_341_);
if (lean_obj_tag(v_type_x3f_340_) == 0)
{
lean_object* v___x_349_; 
lean_dec(v_ids_339_);
lean_dec(v_indent_338_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_fmt_348_);
return v___x_349_;
}
else
{
lean_object* v_val_350_; lean_object* v___x_351_; 
v_val_350_ = lean_ctor_get(v_type_x3f_340_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v_type_x3f_340_, 1);
v___x_351_ = l_Lean_Meta_ppExpr(v_val_350_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_371_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_371_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_356_ = l_List_reverse___redArg(v_ids_339_);
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1));
v___x_358_ = l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(v___x_356_, v___x_357_);
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_box(1);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_a_352_);
v___x_363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_363_, 0, v_indent_338_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_360_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = 0;
v___x_366_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_365_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v_fmt_348_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_367_);
v___x_369_ = v___x_354_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_dec(v_fmt_348_);
lean_dec(v_ids_339_);
lean_dec(v_indent_338_);
return v___x_351_;
}
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_type_x3f_340_);
lean_dec(v_ids_339_);
lean_dec(v_indent_338_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_fmt_341_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(lean_object* v_indent_373_, lean_object* v_ids_374_, lean_object* v_type_x3f_375_, lean_object* v_fmt_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_373_, v_ids_374_, v_type_x3f_375_, v_fmt_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(lean_object* v_e_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l_Lean_Expr_hasMVar(v_e_383_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_e_383_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v_mctx_389_; lean_object* v___x_390_; lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_393_; lean_object* v_cache_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_406_; 
v___x_388_ = lean_st_ref_get(v___y_384_);
v_mctx_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_mctx_389_);
lean_dec(v___x_388_);
v___x_390_ = l_Lean_instantiateMVarsCore(v_mctx_389_, v_e_383_);
v_fst_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v___x_390_);
v___x_393_ = lean_st_ref_take(v___y_384_);
v_cache_394_ = lean_ctor_get(v___x_393_, 1);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_393_, 2);
v_postponed_396_ = lean_ctor_get(v___x_393_, 3);
v_diag_397_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_393_, 0);
lean_dec(v_unused_407_);
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_diag_397_);
lean_inc(v_postponed_396_);
lean_inc(v_zetaDeltaFVarIds_395_);
lean_inc(v_cache_394_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_snd_392_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_snd_392_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_cache_394_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_diag_397_);
v___x_402_ = v_reuseFailAlloc_405_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_st_ref_put(v___y_384_, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_fst_391_);
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg___boxed(lean_object* v_e_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_408_, v___y_409_);
lean_dec(v___y_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(lean_object* v_e_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_412_, v___y_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object* v_e_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(v_e_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
if (lean_obj_tag(v_x_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 1;
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
}
else
{
if (lean_obj_tag(v_x_427_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_val_431_; lean_object* v_val_432_; uint8_t v___x_433_; 
v_val_431_ = lean_ctor_get(v_x_426_, 0);
v_val_432_ = lean_ctor_get(v_x_427_, 0);
v___x_433_ = lean_expr_eqv(v_val_431_, v_val_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_x_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec(v_x_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(lean_object* v_indent_447_, uint8_t v_tactic_448_, lean_object* v_varNames_449_, lean_object* v_prevType_x3f_450_, lean_object* v_fmt_451_, lean_object* v_localDecl_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
if (lean_obj_tag(v_localDecl_452_) == 0)
{
lean_object* v_userName_458_; lean_object* v_type_459_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_501_; 
v_userName_458_ = lean_ctor_get(v_localDecl_452_, 2);
lean_inc(v_userName_458_);
v_type_459_ = lean_ctor_get(v_localDecl_452_, 3);
lean_inc_ref(v_type_459_);
lean_dec_ref_known(v_localDecl_452_, 4);
v___x_460_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_459_, v_a_454_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_501_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_501_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_501_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_varName_465_; uint8_t v___y_467_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_varName_465_ = l_Lean_Name_simpMacroScopes(v_userName_458_);
v___x_497_ = lean_box(0);
v___x_498_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_450_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
lean_inc(v_a_461_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v_a_461_);
v___x_500_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_450_, v___x_499_);
lean_dec_ref_known(v___x_499_, 1);
v___y_467_ = v___x_500_;
goto v___jp_466_;
}
else
{
v___y_467_ = v___x_498_;
goto v___jp_466_;
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
lean_object* v___x_468_; 
lean_del_object(v___x_463_);
v___x_468_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_447_, v_varNames_449_, v_prevType_x3f_450_, v_fmt_451_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_varName_465_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_a_461_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_469_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_474_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_477_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_varName_465_);
lean_dec(v_a_461_);
v_a_482_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_468_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v_prevType_x3f_450_);
lean_dec(v_indent_447_);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v_varName_465_);
lean_ctor_set(v___x_490_, 1, v_varNames_449_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_a_461_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_fmt_451_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_493_);
v___x_495_ = v___x_463_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
uint8_t v_nondep_502_; 
v_nondep_502_ = lean_ctor_get_uint8(v_localDecl_452_, sizeof(void*)*5);
if (v_nondep_502_ == 0)
{
lean_object* v_userName_503_; lean_object* v_type_504_; lean_object* v_value_505_; lean_object* v___x_506_; 
v_userName_503_ = lean_ctor_get(v_localDecl_452_, 2);
lean_inc(v_userName_503_);
v_type_504_ = lean_ctor_get(v_localDecl_452_, 3);
lean_inc_ref(v_type_504_);
v_value_505_ = lean_ctor_get(v_localDecl_452_, 4);
lean_inc_ref(v_value_505_);
lean_dec_ref_known(v_localDecl_452_, 5);
lean_inc(v_indent_447_);
v___x_506_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_447_, v_varNames_449_, v_prevType_x3f_450_, v_fmt_451_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_504_, v_a_454_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l_Lean_Meta_ppExpr(v_a_509_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_564_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_value_505_, v_a_454_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_564_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_564_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_564_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_563_; 
v___x_517_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_448_, v_a_513_, v_a_455_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_563_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_563_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_563_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_varName_522_; lean_object* v___x_523_; lean_object* v_fmtElem_525_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v_varName_522_ = l_Lean_Name_simpMacroScopes(v_userName_503_);
v___x_523_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_507_);
v___x_536_ = 1;
v___x_537_ = l_Lean_Name_toString(v_varName_522_, v___x_536_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 3);
lean_ctor_set(v___x_515_, 0, v___x_537_);
v___x_539_ = v___x_515_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_562_;
goto v_reusejp_538_;
}
v___jp_524_:
{
uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_526_ = 0;
v___x_527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_527_, 0, v_fmtElem_525_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_523_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_box(0);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_528_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_532_);
v___x_534_ = v___x_520_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1));
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_a_511_);
v___x_543_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_a_513_);
lean_dec(v_indent_447_);
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3));
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_542_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v_fmtElem_525_ = v___x_545_;
goto v___jp_524_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_ppExpr(v_a_513_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5));
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_542_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_box(1);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_547_);
v___x_552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_552_, 0, v_indent_447_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_549_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v_fmtElem_525_ = v___x_553_;
goto v___jp_524_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref_known(v___x_542_, 2);
lean_dec(v___x_523_);
lean_del_object(v___x_520_);
lean_dec(v_indent_447_);
v_a_554_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_546_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_546_);
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
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_a_507_);
lean_dec_ref(v_value_505_);
lean_dec(v_userName_503_);
lean_dec(v_indent_447_);
v_a_565_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_510_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_510_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_value_505_);
lean_dec_ref(v_type_504_);
lean_dec(v_userName_503_);
lean_dec(v_indent_447_);
v_a_573_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_506_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_506_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_userName_581_; lean_object* v_type_582_; lean_object* v___x_583_; lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_624_; 
v_userName_581_ = lean_ctor_get(v_localDecl_452_, 2);
lean_inc(v_userName_581_);
v_type_582_ = lean_ctor_get(v_localDecl_452_, 3);
lean_inc_ref(v_type_582_);
lean_dec_ref_known(v_localDecl_452_, 5);
v___x_583_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_582_, v_a_454_);
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_624_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_624_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_624_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_varName_588_; uint8_t v___y_590_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_varName_588_ = l_Lean_Name_simpMacroScopes(v_userName_581_);
v___x_620_ = lean_box(0);
v___x_621_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_450_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
lean_inc(v_a_584_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_a_584_);
v___x_623_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_450_, v___x_622_);
lean_dec_ref_known(v___x_622_, 1);
v___y_590_ = v___x_623_;
goto v___jp_589_;
}
else
{
v___y_590_ = v___x_621_;
goto v___jp_589_;
}
v___jp_589_:
{
if (v___y_590_ == 0)
{
lean_object* v___x_591_; 
lean_del_object(v___x_586_);
v___x_591_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_447_, v_varNames_449_, v_prevType_x3f_450_, v_fmt_451_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_604_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_604_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_604_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_604_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v_varName_588_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_a_584_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_a_592_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_600_);
v___x_602_ = v___x_594_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_varName_588_);
lean_dec(v_a_584_);
v_a_605_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_591_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_591_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec(v_prevType_x3f_450_);
lean_dec(v_indent_447_);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v_varName_588_);
lean_ctor_set(v___x_613_, 1, v_varNames_449_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_584_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_fmt_451_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_616_);
v___x_618_ = v___x_586_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___boxed(lean_object* v_indent_625_, lean_object* v_tactic_626_, lean_object* v_varNames_627_, lean_object* v_prevType_x3f_628_, lean_object* v_fmt_629_, lean_object* v_localDecl_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_tactic_boxed_636_; lean_object* v_res_637_; 
v_tactic_boxed_636_ = lean_unbox(v_tactic_626_);
v_res_637_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v_indent_625_, v_tactic_boxed_636_, v_varNames_627_, v_prevType_x3f_628_, v_fmt_629_, v_localDecl_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(lean_object* v_lctx_638_, lean_object* v_localInsts_639_, lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_638_, v_localInsts_639_, v_x_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_a_655_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg___boxed(lean_object* v_lctx_663_, lean_object* v_localInsts_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_663_, v_localInsts_664_, v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(lean_object* v_00_u03b1_672_, lean_object* v_lctx_673_, lean_object* v_localInsts_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_lctx_673_, v_localInsts_674_, v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___boxed(lean_object* v_00_u03b1_682_, lean_object* v_lctx_683_, lean_object* v_localInsts_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(v_00_u03b1_682_, v_lctx_683_, v_localInsts_684_, v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(2u);
v___x_693_ = lean_nat_to_int(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(uint8_t v___x_694_, uint8_t v___x_695_, uint8_t v___x_696_, lean_object* v_as_697_, size_t v_i_698_, size_t v_stop_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_a_707_; lean_object* v___y_712_; uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_eq(v_i_698_, v_stop_699_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_array_uget_borrowed(v_as_697_, v_i_698_);
if (lean_obj_tag(v___x_715_) == 0)
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
else
{
lean_object* v_snd_716_; lean_object* v_val_717_; lean_object* v_fst_718_; lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_721_; 
v_snd_716_ = lean_ctor_get(v_b_700_, 1);
v_val_717_ = lean_ctor_get(v___x_715_, 0);
v_fst_718_ = lean_ctor_get(v_b_700_, 0);
v_fst_719_ = lean_ctor_get(v_snd_716_, 0);
v_snd_720_ = lean_ctor_get(v_snd_716_, 1);
v___x_721_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
if (v___x_696_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_LocalDecl_isAuxDecl(v_val_717_);
if (v___x_726_ == 0)
{
goto v___jp_722_;
}
else
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
}
else
{
goto v___jp_722_;
}
v___jp_722_:
{
if (v___x_694_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_LocalDecl_isImplementationDetail(v_val_717_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_inc(v_fst_718_);
lean_dec_ref(v_b_700_);
lean_inc(v_val_717_);
v___x_724_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_721_, v___x_695_, v_fst_718_, v_fst_719_, v_snd_720_, v_val_717_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v___y_712_ = v___x_724_;
goto v___jp_711_;
}
else
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
}
else
{
lean_object* v___x_725_; 
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_inc(v_fst_718_);
lean_dec_ref(v_b_700_);
lean_inc(v_val_717_);
v___x_725_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_721_, v___x_695_, v_fst_718_, v_fst_719_, v_snd_720_, v_val_717_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v___y_712_ = v___x_725_;
goto v___jp_711_;
}
}
}
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_700_);
return v___x_727_;
}
v___jp_706_:
{
size_t v___x_708_; size_t v___x_709_; 
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_698_, v___x_708_);
v_i_698_ = v___x_709_;
v_b_700_ = v_a_707_;
goto _start;
}
v___jp_711_:
{
if (lean_obj_tag(v___y_712_) == 0)
{
lean_object* v_a_713_; 
v_a_713_ = lean_ctor_get(v___y_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___y_712_, 1);
v_a_707_ = v_a_713_;
goto v___jp_706_;
}
else
{
return v___y_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_stop_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
uint8_t v___x_4421__boxed_740_; uint8_t v___x_4422__boxed_741_; uint8_t v___x_4423__boxed_742_; size_t v_i_boxed_743_; size_t v_stop_boxed_744_; lean_object* v_res_745_; 
v___x_4421__boxed_740_ = lean_unbox(v___x_728_);
v___x_4422__boxed_741_ = lean_unbox(v___x_729_);
v___x_4423__boxed_742_ = lean_unbox(v___x_730_);
v_i_boxed_743_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_stop_boxed_744_ = lean_unbox_usize(v_stop_733_);
lean_dec(v_stop_733_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_4421__boxed_740_, v___x_4422__boxed_741_, v___x_4423__boxed_742_, v_as_731_, v_i_boxed_743_, v_stop_boxed_744_, v_b_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_as_731_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(uint8_t v___x_746_, uint8_t v___x_747_, uint8_t v___x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
lean_object* v_cs_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_769_; 
v_cs_756_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_769_ == 0)
{
v___x_758_ = v_x_749_;
v_isShared_759_ = v_isSharedCheck_769_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_cs_756_);
lean_dec(v_x_749_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_769_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_cs_756_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v_cs_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_x_750_);
v___x_764_ = v___x_758_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_x_750_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
lean_del_object(v___x_758_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_761_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_746_, v___x_747_, v___x_748_, v_cs_756_, v___x_766_, v___x_767_, v_x_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_cs_756_);
return v___x_768_;
}
}
}
else
{
lean_object* v_vs_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_783_; 
v_vs_770_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_783_ == 0)
{
v___x_772_ = v_x_749_;
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_vs_770_);
lean_dec(v_x_749_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_array_get_size(v_vs_770_);
v___x_776_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v_vs_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v_x_750_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_x_750_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
lean_del_object(v___x_772_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_775_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_746_, v___x_747_, v___x_748_, v_vs_770_, v___x_780_, v___x_781_, v_x_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_vs_770_);
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(uint8_t v___x_784_, uint8_t v___x_785_, uint8_t v___x_786_, lean_object* v_as_787_, size_t v_i_788_, size_t v_stop_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_eq(v_i_788_, v_stop_789_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_array_uget_borrowed(v_as_787_, v_i_788_);
lean_inc(v___x_797_);
v___x_798_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_784_, v___x_785_, v___x_786_, v___x_797_, v_b_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; size_t v___x_800_; size_t v___x_801_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_i_788_, v___x_800_);
v_i_788_ = v___x_801_;
v_b_790_ = v_a_799_;
goto _start;
}
else
{
return v___x_798_;
}
}
else
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_b_790_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v___x_806_, lean_object* v_as_807_, lean_object* v_i_808_, lean_object* v_stop_809_, lean_object* v_b_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___x_4492__boxed_816_; uint8_t v___x_4493__boxed_817_; uint8_t v___x_4494__boxed_818_; size_t v_i_boxed_819_; size_t v_stop_boxed_820_; lean_object* v_res_821_; 
v___x_4492__boxed_816_ = lean_unbox(v___x_804_);
v___x_4493__boxed_817_ = lean_unbox(v___x_805_);
v___x_4494__boxed_818_ = lean_unbox(v___x_806_);
v_i_boxed_819_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_stop_boxed_820_ = lean_unbox_usize(v_stop_809_);
lean_dec(v_stop_809_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_4492__boxed_816_, v___x_4493__boxed_817_, v___x_4494__boxed_818_, v_as_807_, v_i_boxed_819_, v_stop_boxed_820_, v_b_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v_as_807_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_4509__boxed_832_; uint8_t v___x_4510__boxed_833_; uint8_t v___x_4511__boxed_834_; lean_object* v_res_835_; 
v___x_4509__boxed_832_ = lean_unbox(v___x_822_);
v___x_4510__boxed_833_ = lean_unbox(v___x_823_);
v___x_4511__boxed_834_ = lean_unbox(v___x_824_);
v_res_835_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_4509__boxed_832_, v___x_4510__boxed_833_, v___x_4511__boxed_834_, v_x_825_, v_x_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_835_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(uint8_t v___x_837_, uint8_t v___x_838_, uint8_t v___x_839_, lean_object* v_x_840_, size_t v_x_841_, size_t v_x_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_cs_849_; lean_object* v___x_850_; size_t v___x_851_; lean_object* v_j_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v_cs_849_ = lean_ctor_get(v_x_840_, 0);
lean_inc_ref(v_cs_849_);
lean_dec_ref_known(v_x_840_, 1);
v___x_850_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0);
v___x_851_ = lean_usize_shift_right(v_x_841_, v_x_842_);
v_j_852_ = lean_usize_to_nat(v___x_851_);
v___x_853_ = lean_array_get_borrowed(v___x_850_, v_cs_849_, v_j_852_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_shift_left(v___x_854_, v_x_842_);
v___x_856_ = lean_usize_sub(v___x_855_, v___x_854_);
v___x_857_ = lean_usize_land(v_x_841_, v___x_856_);
v___x_858_ = ((size_t)5ULL);
v___x_859_ = lean_usize_sub(v_x_842_, v___x_858_);
lean_inc(v___x_853_);
v___x_860_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_837_, v___x_838_, v___x_839_, v___x_853_, v___x_857_, v___x_859_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_j_852_, v___x_862_);
lean_dec(v_j_852_);
v___x_864_ = lean_array_get_size(v_cs_849_);
v___x_865_ = lean_nat_dec_lt(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec(v___x_863_);
lean_dec(v_a_861_);
lean_dec_ref(v_cs_849_);
return v___x_860_;
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
lean_dec_ref_known(v___x_860_, 1);
v___x_866_ = lean_usize_of_nat(v___x_863_);
lean_dec(v___x_863_);
v___x_867_ = lean_usize_of_nat(v___x_864_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_837_, v___x_838_, v___x_839_, v_cs_849_, v___x_866_, v___x_867_, v_a_861_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec_ref(v_cs_849_);
return v___x_868_;
}
}
else
{
lean_dec(v_j_852_);
lean_dec_ref(v_cs_849_);
return v___x_860_;
}
}
else
{
lean_object* v_vs_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_vs_869_ = lean_ctor_get(v_x_840_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_882_ == 0)
{
v___x_871_ = v_x_840_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_vs_869_);
lean_dec(v_x_840_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = lean_usize_to_nat(v_x_841_);
v___x_874_ = lean_array_get_size(v_vs_869_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v___x_873_);
lean_dec_ref(v_vs_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 0);
lean_ctor_set(v___x_871_, 0, v_x_843_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_x_843_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; 
lean_del_object(v___x_871_);
v___x_879_ = lean_usize_of_nat(v___x_873_);
lean_dec(v___x_873_);
v___x_880_ = lean_usize_of_nat(v___x_874_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_837_, v___x_838_, v___x_839_, v_vs_869_, v___x_879_, v___x_880_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec_ref(v_vs_869_);
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_4621__boxed_895_; uint8_t v___x_4622__boxed_896_; uint8_t v___x_4623__boxed_897_; size_t v_x_4625__boxed_898_; size_t v_x_4626__boxed_899_; lean_object* v_res_900_; 
v___x_4621__boxed_895_ = lean_unbox(v___x_883_);
v___x_4622__boxed_896_ = lean_unbox(v___x_884_);
v___x_4623__boxed_897_ = lean_unbox(v___x_885_);
v_x_4625__boxed_898_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_x_4626__boxed_899_ = lean_unbox_usize(v_x_888_);
lean_dec(v_x_888_);
v_res_900_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_4621__boxed_895_, v___x_4622__boxed_896_, v___x_4623__boxed_897_, v_x_886_, v_x_4625__boxed_898_, v_x_4626__boxed_899_, v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(uint8_t v___x_901_, uint8_t v___x_902_, uint8_t v___x_903_, lean_object* v_t_904_, lean_object* v_init_905_, lean_object* v_start_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_nat_dec_eq(v_start_906_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v_root_914_; lean_object* v_tail_915_; size_t v_shift_916_; lean_object* v_tailOff_917_; uint8_t v___x_918_; 
v_root_914_ = lean_ctor_get(v_t_904_, 0);
lean_inc_ref(v_root_914_);
v_tail_915_ = lean_ctor_get(v_t_904_, 1);
lean_inc_ref(v_tail_915_);
v_shift_916_ = lean_ctor_get_usize(v_t_904_, 4);
v_tailOff_917_ = lean_ctor_get(v_t_904_, 3);
lean_inc(v_tailOff_917_);
lean_dec_ref(v_t_904_);
v___x_918_ = lean_nat_dec_le(v_tailOff_917_, v_start_906_);
if (v___x_918_ == 0)
{
size_t v___x_919_; lean_object* v___x_920_; 
lean_dec(v_tailOff_917_);
v___x_919_ = lean_usize_of_nat(v_start_906_);
v___x_920_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_901_, v___x_902_, v___x_903_, v_root_914_, v___x_919_, v_shift_916_, v_init_905_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
v___x_922_ = lean_array_get_size(v_tail_915_);
v___x_923_ = lean_nat_dec_lt(v___x_912_, v___x_922_);
if (v___x_923_ == 0)
{
lean_dec(v_a_921_);
lean_dec_ref(v_tail_915_);
return v___x_920_;
}
else
{
size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_924_ = ((size_t)0ULL);
v___x_925_ = lean_usize_of_nat(v___x_922_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_901_, v___x_902_, v___x_903_, v_tail_915_, v___x_924_, v___x_925_, v_a_921_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec_ref(v_tail_915_);
return v___x_926_;
}
}
else
{
lean_dec_ref(v_tail_915_);
return v___x_920_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
lean_dec_ref(v_root_914_);
v___x_927_ = lean_nat_sub(v_start_906_, v_tailOff_917_);
lean_dec(v_tailOff_917_);
v___x_928_ = lean_array_get_size(v_tail_915_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec(v___x_927_);
lean_dec_ref(v_tail_915_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_init_905_);
return v___x_930_;
}
else
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_usize_of_nat(v___x_927_);
lean_dec(v___x_927_);
v___x_932_ = lean_usize_of_nat(v___x_928_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_901_, v___x_902_, v___x_903_, v_tail_915_, v___x_931_, v___x_932_, v_init_905_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec_ref(v_tail_915_);
return v___x_933_;
}
}
}
else
{
lean_object* v_root_934_; lean_object* v_tail_935_; lean_object* v___x_936_; 
v_root_934_ = lean_ctor_get(v_t_904_, 0);
lean_inc_ref(v_root_934_);
v_tail_935_ = lean_ctor_get(v_t_904_, 1);
lean_inc_ref(v_tail_935_);
lean_dec_ref(v_t_904_);
v___x_936_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_901_, v___x_902_, v___x_903_, v_root_934_, v_init_905_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
v___x_938_ = lean_array_get_size(v_tail_935_);
v___x_939_ = lean_nat_dec_lt(v___x_912_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v_a_937_);
lean_dec_ref(v_tail_935_);
return v___x_936_;
}
else
{
size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; 
lean_dec_ref_known(v___x_936_, 1);
v___x_940_ = ((size_t)0ULL);
v___x_941_ = lean_usize_of_nat(v___x_938_);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_901_, v___x_902_, v___x_903_, v_tail_935_, v___x_940_, v___x_941_, v_a_937_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec_ref(v_tail_935_);
return v___x_942_;
}
}
else
{
lean_dec_ref(v_tail_935_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object* v___x_943_, lean_object* v___x_944_, lean_object* v___x_945_, lean_object* v_t_946_, lean_object* v_init_947_, lean_object* v_start_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_4725__boxed_954_; uint8_t v___x_4726__boxed_955_; uint8_t v___x_4727__boxed_956_; lean_object* v_res_957_; 
v___x_4725__boxed_954_ = lean_unbox(v___x_943_);
v___x_4726__boxed_955_ = lean_unbox(v___x_944_);
v___x_4727__boxed_956_ = lean_unbox(v___x_945_);
v_res_957_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_4725__boxed_954_, v___x_4726__boxed_955_, v___x_4727__boxed_956_, v_t_946_, v_init_947_, v_start_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v_start_948_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(uint8_t v___x_958_, uint8_t v___x_959_, uint8_t v___x_960_, lean_object* v_lctx_961_, lean_object* v_init_962_, lean_object* v_start_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_decls_969_; lean_object* v___x_970_; 
v_decls_969_ = lean_ctor_get(v_lctx_961_, 1);
lean_inc_ref(v_decls_969_);
lean_dec_ref(v_lctx_961_);
v___x_970_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_958_, v___x_959_, v___x_960_, v_decls_969_, v_init_962_, v_start_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v_lctx_974_, lean_object* v_init_975_, lean_object* v_start_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_4801__boxed_982_; uint8_t v___x_4802__boxed_983_; uint8_t v___x_4803__boxed_984_; lean_object* v_res_985_; 
v___x_4801__boxed_982_ = lean_unbox(v___x_971_);
v___x_4802__boxed_983_ = lean_unbox(v___x_972_);
v___x_4803__boxed_984_ = lean_unbox(v___x_973_);
v_res_985_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_4801__boxed_982_, v___x_4802__boxed_983_, v___x_4803__boxed_984_, v_lctx_974_, v_init_975_, v_start_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_start_976_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(uint8_t v___x_989_, uint8_t v___x_990_, uint8_t v___x_991_, lean_object* v_fst_992_, lean_object* v___x_993_, lean_object* v___x_994_, lean_object* v___x_995_, lean_object* v_type_996_, lean_object* v_val_997_, lean_object* v_userName_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_989_, v___x_990_, v___x_991_, v_fst_992_, v___x_993_, v___x_994_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v_snd_1006_; lean_object* v_fst_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1064_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v_snd_1006_ = lean_ctor_get(v_a_1005_, 1);
v_fst_1007_ = lean_ctor_get(v_a_1005_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1009_ = v_a_1005_;
v_isShared_1010_ = v_isSharedCheck_1064_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1006_);
lean_inc(v_fst_1007_);
lean_dec(v_a_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1064_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1063_; 
v_fst_1011_ = lean_ctor_get(v_snd_1006_, 0);
v_snd_1012_ = lean_ctor_get(v_snd_1006_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_1006_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1014_ = v_snd_1006_;
v_isShared_1015_ = v_isSharedCheck_1063_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_inc(v_fst_1011_);
lean_dec(v_snd_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1063_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; 
lean_inc(v___x_995_);
v___x_1016_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v___x_995_, v_fst_1007_, v_fst_1011_, v_snd_1012_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1062_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1062_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1062_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1061_; 
v___x_1021_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_996_, v___y_1000_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Meta_ppExpr(v_a_1022_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1060_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1060_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1060_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_1017_);
v___x_1032_ = l_Lean_Meta_getGoalPrefix(v_val_997_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 3);
lean_ctor_set(v___x_1024_, 0, v___x_1032_);
v___x_1034_ = v___x_1024_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 5);
lean_ctor_set(v___x_1014_, 1, v___x_1034_);
lean_ctor_set(v___x_1014_, 0, v___x_1031_);
v___x_1036_ = v___x_1014_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 4);
lean_ctor_set(v___x_1009_, 1, v_a_1027_);
lean_ctor_set(v___x_1009_, 0, v___x_995_);
v___x_1038_ = v___x_1009_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_a_1027_);
v___x_1038_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1036_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
if (lean_obj_tag(v_userName_998_) == 0)
{
lean_object* v___x_1041_; 
lean_del_object(v___x_1019_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1039_);
v___x_1041_ = v___x_1029_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1043_ = ((lean_object*)(l_Lean_Meta_ppGoal___lam__0___closed__1));
v___x_1044_ = l_Lean_Name_eraseMacroScopes(v_userName_998_);
v___x_1045_ = 1;
v___x_1046_ = l_Lean_Name_toString(v___x_1044_, v___x_1045_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 3);
lean_ctor_set(v___x_1019_, 0, v___x_1046_);
v___x_1048_ = v___x_1019_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1043_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_1039_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1052_);
v___x_1054_ = v___x_1029_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
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
}
}
}
else
{
lean_del_object(v___x_1024_);
lean_del_object(v___x_1019_);
lean_dec(v_a_1017_);
lean_del_object(v___x_1014_);
lean_del_object(v___x_1009_);
lean_dec(v___x_995_);
return v___x_1026_;
}
}
}
}
else
{
lean_del_object(v___x_1014_);
lean_del_object(v___x_1009_);
lean_dec_ref(v_type_996_);
lean_dec(v___x_995_);
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_type_996_);
lean_dec(v___x_995_);
v_a_1065_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1004_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1004_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_fst_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_type_1080_, lean_object* v_val_1081_, lean_object* v_userName_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v___x_4836__boxed_1088_; uint8_t v___x_4837__boxed_1089_; uint8_t v___x_4838__boxed_1090_; lean_object* v_res_1091_; 
v___x_4836__boxed_1088_ = lean_unbox(v___x_1073_);
v___x_4837__boxed_1089_ = lean_unbox(v___x_1074_);
v___x_4838__boxed_1090_ = lean_unbox(v___x_1075_);
v_res_1091_ = l_Lean_Meta_ppGoal___lam__0(v___x_4836__boxed_1088_, v___x_4837__boxed_1089_, v___x_4838__boxed_1090_, v_fst_1076_, v___x_1077_, v___x_1078_, v___x_1079_, v_type_1080_, v_val_1081_, v_userName_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_userName_1082_);
lean_dec_ref(v_val_1081_);
lean_dec(v___x_1078_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object* v_mvarId_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_mctx_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_st_ref_get(v_a_1103_);
v_mctx_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_mctx_1108_);
lean_dec(v___x_1107_);
v___x_1109_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1108_, v_mvarId_1101_);
lean_dec_ref(v_mctx_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__1));
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_toCold_1112_; lean_object* v_val_1113_; lean_object* v_options_1114_; lean_object* v_userName_1115_; lean_object* v_lctx_1116_; lean_object* v_type_1117_; lean_object* v_localInstances_1118_; uint8_t v_kind_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_fst_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v_toCold_1112_ = lean_ctor_get(v_a_1104_, 0);
v_val_1113_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1109_, 1);
v_options_1114_ = lean_ctor_get(v_toCold_1112_, 2);
v_userName_1115_ = lean_ctor_get(v_val_1113_, 0);
lean_inc(v_userName_1115_);
v_lctx_1116_ = lean_ctor_get(v_val_1113_, 1);
v_type_1117_ = lean_ctor_get(v_val_1113_, 2);
lean_inc_ref(v_type_1117_);
v_localInstances_1118_ = lean_ctor_get(v_val_1113_, 4);
lean_inc_ref(v_localInstances_1118_);
v_kind_1119_ = lean_ctor_get_uint8(v_val_1113_, sizeof(void*)*7);
v___x_1120_ = l_Lean_Meta_pp_auxDecls;
v___x_1121_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1114_, v___x_1120_);
v___x_1122_ = l_Lean_Meta_pp_implementationDetailHyps;
v___x_1123_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1114_, v___x_1122_);
v___x_1124_ = lean_box(1);
lean_inc_ref(v_options_1114_);
v___x_1125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1125_, 0, v_options_1114_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_ctor_set(v___x_1125_, 2, v___x_1124_);
lean_inc_ref(v_lctx_1116_);
v___x_1126_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1116_, v___x_1125_);
v_fst_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_n(v_fst_1127_, 2);
lean_dec_ref(v___x_1126_);
v___x_1128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
v___x_1129_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_1119_);
v___x_1130_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__3));
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_box(v___x_1123_);
v___x_1133_ = lean_box(v___x_1129_);
v___x_1134_ = lean_box(v___x_1121_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1135_, 0, v___x_1132_);
lean_closure_set(v___f_1135_, 1, v___x_1133_);
lean_closure_set(v___f_1135_, 2, v___x_1134_);
lean_closure_set(v___f_1135_, 3, v_fst_1127_);
lean_closure_set(v___f_1135_, 4, v___x_1130_);
lean_closure_set(v___f_1135_, 5, v___x_1131_);
lean_closure_set(v___f_1135_, 6, v___x_1128_);
lean_closure_set(v___f_1135_, 7, v_type_1117_);
lean_closure_set(v___f_1135_, 8, v_val_1113_);
lean_closure_set(v___f_1135_, 9, v_userName_1115_);
v___x_1136_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_fst_1127_, v_localInstances_1118_, v___f_1135_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object* v_mvarId_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Meta_ppGoal(v_mvarId_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_mvarId_1137_);
return v_res_1143_;
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
