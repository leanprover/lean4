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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_simpMacroScopes(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
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
lean_object* v_options_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_options_247_ = lean_ctor_get(v_a_232_, 2);
v___x_248_ = l_Lean_Meta_pp_showLetValues;
v___x_249_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___y_253_; 
v___x_250_ = l_Lean_Meta_pp_showLetValues_threshold;
v___x_251_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_247_, v___x_250_);
if (v_tactic_230_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___y_253_ = v___x_255_;
goto v___jp_252_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = l_Lean_Meta_pp_showLetValues_tactic_threshold;
v___x_257_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_247_, v___x_256_);
v___y_253_ = v___x_257_;
goto v___jp_252_;
}
v___jp_252_:
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_le(v___x_251_, v___y_253_);
if (v___x_254_ == 0)
{
lean_dec(v___y_253_);
v___y_242_ = v___x_251_;
goto v___jp_241_;
}
else
{
lean_dec(v___x_251_);
v___y_242_ = v___y_253_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(v___x_246_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(v___x_246_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(lean_object* v_tactic_262_, lean_object* v_e_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
uint8_t v_tactic_boxed_266_; lean_object* v_res_267_; 
v_tactic_boxed_266_ = lean_unbox(v_tactic_262_);
v_res_267_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_boxed_266_, v_e_263_, v_a_264_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_e_263_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue(uint8_t v_tactic_268_, lean_object* v_e_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_268_, v_e_269_, v_a_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(lean_object* v_tactic_276_, lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
uint8_t v_tactic_boxed_283_; lean_object* v_res_284_; 
v_tactic_boxed_283_ = lean_unbox(v_tactic_276_);
v_res_284_ = l_Lean_Meta_ppGoal_shouldShowLetValue(v_tactic_boxed_283_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec_ref(v_e_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object* v_fmt_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = l_Std_Format_isNil(v_fmt_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v_fmt_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
else
{
return v_fmt_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object* v_mvarDecl_294_){
_start:
{
lean_object* v_type_295_; lean_object* v___x_296_; 
v_type_295_ = lean_ctor_get(v_mvarDecl_294_, 2);
v___x_296_ = l_Lean_isLHSGoal_x3f(v_type_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__0));
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = ((lean_object*)(l_Lean_Meta_getGoalPrefix___closed__1));
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object* v_mvarDecl_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_299_);
lean_dec_ref(v_mvarDecl_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_dec(v_x_301_);
return v_x_302_;
}
else
{
lean_object* v_head_304_; lean_object* v_tail_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_317_; 
v_head_304_ = lean_ctor_get(v_x_303_, 0);
v_tail_305_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_317_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_317_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_tail_305_);
lean_inc(v_head_304_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_317_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
lean_inc(v_x_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 5);
lean_ctor_set(v___x_307_, 1, v_x_301_);
lean_ctor_set(v___x_307_, 0, v_x_302_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_x_301_);
v___x_310_ = v_reuseFailAlloc_316_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = 1;
v___x_312_ = l_Lean_Name_toString(v_head_304_, v___x_311_);
v___x_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_310_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v_x_302_ = v___x_314_;
v_x_303_ = v_tail_305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v___x_320_; 
lean_dec(v_x_319_);
v___x_320_ = lean_box(0);
return v___x_320_;
}
else
{
lean_object* v_tail_321_; 
v_tail_321_ = lean_ctor_get(v_x_318_, 1);
if (lean_obj_tag(v_tail_321_) == 0)
{
lean_object* v_head_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_x_319_);
v_head_322_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_head_322_);
lean_dec_ref_known(v_x_318_, 2);
v___x_323_ = 1;
v___x_324_ = l_Lean_Name_toString(v_head_322_, v___x_323_);
v___x_325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v_head_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_inc(v_tail_321_);
v_head_326_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_head_326_);
lean_dec_ref_known(v_x_318_, 2);
v___x_327_ = 1;
v___x_328_ = l_Lean_Name_toString(v_head_326_, v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(v_x_319_, v___x_329_, v_tail_321_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(lean_object* v_indent_337_, lean_object* v_ids_338_, lean_object* v_type_x3f_339_, lean_object* v_fmt_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_List_isEmpty___redArg(v_ids_338_);
if (v___x_346_ == 0)
{
lean_object* v_fmt_347_; 
v_fmt_347_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_fmt_340_);
if (lean_obj_tag(v_type_x3f_339_) == 0)
{
lean_object* v___x_348_; 
lean_dec(v_ids_338_);
lean_dec(v_indent_337_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_fmt_347_);
return v___x_348_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_350_; 
v_val_349_ = lean_ctor_get(v_type_x3f_339_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v_type_x3f_339_, 1);
v___x_350_ = l_Lean_Meta_ppExpr(v_val_349_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_370_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_355_ = l_List_reverse___redArg(v_ids_338_);
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1));
v___x_357_ = l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(v___x_355_, v___x_356_);
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3));
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_box(1);
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_351_);
v___x_362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_362_, 0, v_indent_337_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_359_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v_fmt_347_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_366_);
v___x_368_ = v___x_353_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_dec(v_fmt_347_);
lean_dec(v_ids_338_);
lean_dec(v_indent_337_);
return v___x_350_;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_type_x3f_339_);
lean_dec(v_ids_338_);
lean_dec(v_indent_337_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_fmt_340_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(lean_object* v_indent_372_, lean_object* v_ids_373_, lean_object* v_type_x3f_374_, lean_object* v_fmt_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v_indent_372_, v_ids_373_, v_type_x3f_374_, v_fmt_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(lean_object* v_e_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = l_Lean_Expr_hasMVar(v_e_382_);
v___x_386_ = lean_bool_not(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v_mctx_388_; lean_object* v___x_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_392_; lean_object* v_cache_393_; lean_object* v_zetaDeltaFVarIds_394_; lean_object* v_postponed_395_; lean_object* v_diag_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_405_; 
v___x_387_ = lean_st_ref_get(v___y_383_);
v_mctx_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_mctx_388_);
lean_dec(v___x_387_);
v___x_389_ = l_Lean_instantiateMVarsCore(v_mctx_388_, v_e_382_);
v_fst_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v___x_389_, 1);
lean_inc(v_snd_391_);
lean_dec_ref(v___x_389_);
v___x_392_ = lean_st_ref_take(v___y_383_);
v_cache_393_ = lean_ctor_get(v___x_392_, 1);
v_zetaDeltaFVarIds_394_ = lean_ctor_get(v___x_392_, 2);
v_postponed_395_ = lean_ctor_get(v___x_392_, 3);
v_diag_396_ = lean_ctor_get(v___x_392_, 4);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_392_, 0);
lean_dec(v_unused_406_);
v___x_398_ = v___x_392_;
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_diag_396_);
lean_inc(v_postponed_395_);
lean_inc(v_zetaDeltaFVarIds_394_);
lean_inc(v_cache_393_);
lean_dec(v___x_392_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_snd_391_);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_snd_391_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_cache_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_zetaDeltaFVarIds_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_postponed_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_diag_396_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_st_ref_set(v___y_383_, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v_fst_390_);
return v___x_403_;
}
}
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_e_382_);
return v___x_407_;
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
lean_object* v_a_707_; uint8_t v___x_711_; 
v___x_711_ = lean_usize_dec_eq(v_i_698_, v_stop_699_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_array_uget_borrowed(v_as_697_, v_i_698_);
if (lean_obj_tag(v___x_712_) == 0)
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
else
{
lean_object* v_snd_713_; lean_object* v_val_714_; lean_object* v_fst_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___x_718_; uint8_t v___y_720_; uint8_t v___y_724_; uint8_t v___x_727_; 
v_snd_713_ = lean_ctor_get(v_b_700_, 1);
v_val_714_ = lean_ctor_get(v___x_712_, 0);
v_fst_715_ = lean_ctor_get(v_b_700_, 0);
v_fst_716_ = lean_ctor_get(v_snd_713_, 0);
v_snd_717_ = lean_ctor_get(v_snd_713_, 1);
v___x_718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
v___x_727_ = lean_bool_not(v___x_696_);
if (v___x_727_ == 0)
{
v___y_724_ = v___x_727_;
goto v___jp_723_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_LocalDecl_isAuxDecl(v_val_714_);
v___y_724_ = v___x_728_;
goto v___jp_723_;
}
v___jp_719_:
{
if (v___y_720_ == 0)
{
lean_object* v___x_721_; 
lean_inc(v_snd_717_);
lean_inc(v_fst_716_);
lean_inc(v_fst_715_);
lean_dec_ref(v_b_700_);
lean_inc(v_val_714_);
v___x_721_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(v___x_718_, v___x_694_, v_fst_715_, v_fst_716_, v_snd_717_, v_val_714_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v_a_707_ = v_a_722_;
goto v___jp_706_;
}
else
{
return v___x_721_;
}
}
else
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
}
v___jp_723_:
{
if (v___y_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = lean_bool_not(v___x_695_);
if (v___x_725_ == 0)
{
v___y_720_ = v___x_725_;
goto v___jp_719_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_LocalDecl_isImplementationDetail(v_val_714_);
v___y_720_ = v___x_726_;
goto v___jp_719_;
}
}
else
{
v_a_707_ = v_b_700_;
goto v___jp_706_;
}
}
}
}
else
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_b_700_);
return v___x_729_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___x_4885__boxed_742_; uint8_t v___x_4886__boxed_743_; uint8_t v___x_4887__boxed_744_; size_t v_i_boxed_745_; size_t v_stop_boxed_746_; lean_object* v_res_747_; 
v___x_4885__boxed_742_ = lean_unbox(v___x_730_);
v___x_4886__boxed_743_ = lean_unbox(v___x_731_);
v___x_4887__boxed_744_ = lean_unbox(v___x_732_);
v_i_boxed_745_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_746_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_4885__boxed_742_, v___x_4886__boxed_743_, v___x_4887__boxed_744_, v_as_733_, v_i_boxed_745_, v_stop_boxed_746_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_as_733_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(uint8_t v___x_748_, uint8_t v___x_749_, uint8_t v___x_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v_cs_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_778_; 
v_cs_758_ = lean_ctor_get(v_x_751_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_778_ == 0)
{
v___x_760_ = v_x_751_;
v_isShared_761_ = v_isSharedCheck_778_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_cs_758_);
lean_dec(v_x_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_778_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_array_get_size(v_cs_758_);
v___x_764_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v_cs_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_x_752_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_x_752_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
uint8_t v___x_768_; 
v___x_768_ = lean_nat_dec_le(v___x_763_, v___x_763_);
if (v___x_768_ == 0)
{
if (v___x_764_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v_cs_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_x_752_);
v___x_770_ = v___x_760_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_x_752_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
lean_del_object(v___x_760_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_763_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_748_, v___x_749_, v___x_750_, v_cs_758_, v___x_772_, v___x_773_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_cs_758_);
return v___x_774_;
}
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
lean_del_object(v___x_760_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_763_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_748_, v___x_749_, v___x_750_, v_cs_758_, v___x_775_, v___x_776_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_cs_758_);
return v___x_777_;
}
}
}
}
else
{
lean_object* v_vs_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_799_; 
v_vs_779_ = lean_ctor_get(v_x_751_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_799_ == 0)
{
v___x_781_ = v_x_751_;
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_vs_779_);
lean_dec(v_x_751_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_array_get_size(v_vs_779_);
v___x_785_ = lean_nat_dec_lt(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_vs_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
lean_ctor_set(v___x_781_, 0, v_x_752_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_x_752_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_le(v___x_784_, v___x_784_);
if (v___x_789_ == 0)
{
if (v___x_785_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v_vs_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
lean_ctor_set(v___x_781_, 0, v_x_752_);
v___x_791_ = v___x_781_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_x_752_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_781_);
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_784_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_748_, v___x_749_, v___x_750_, v_vs_779_, v___x_793_, v___x_794_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_vs_779_);
return v___x_795_;
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_781_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_784_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_748_, v___x_749_, v___x_750_, v_vs_779_, v___x_796_, v___x_797_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_vs_779_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(uint8_t v___x_800_, uint8_t v___x_801_, uint8_t v___x_802_, lean_object* v_as_803_, size_t v_i_804_, size_t v_stop_805_, lean_object* v_b_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_eq(v_i_804_, v_stop_805_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_uget_borrowed(v_as_803_, v_i_804_);
lean_inc(v___x_813_);
v___x_814_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_800_, v___x_801_, v___x_802_, v___x_813_, v_b_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; size_t v___x_816_; size_t v___x_817_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_804_, v___x_816_);
v_i_804_ = v___x_817_;
v_b_806_ = v_a_815_;
goto _start;
}
else
{
return v___x_814_;
}
}
else
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_b_806_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_as_823_, lean_object* v_i_824_, lean_object* v_stop_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_4960__boxed_832_; uint8_t v___x_4961__boxed_833_; uint8_t v___x_4962__boxed_834_; size_t v_i_boxed_835_; size_t v_stop_boxed_836_; lean_object* v_res_837_; 
v___x_4960__boxed_832_ = lean_unbox(v___x_820_);
v___x_4961__boxed_833_ = lean_unbox(v___x_821_);
v___x_4962__boxed_834_ = lean_unbox(v___x_822_);
v_i_boxed_835_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_stop_boxed_836_ = lean_unbox_usize(v_stop_825_);
lean_dec(v_stop_825_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_4960__boxed_832_, v___x_4961__boxed_833_, v___x_4962__boxed_834_, v_as_823_, v_i_boxed_835_, v_stop_boxed_836_, v_b_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_as_823_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(lean_object* v___x_838_, lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_4977__boxed_848_; uint8_t v___x_4978__boxed_849_; uint8_t v___x_4979__boxed_850_; lean_object* v_res_851_; 
v___x_4977__boxed_848_ = lean_unbox(v___x_838_);
v___x_4978__boxed_849_ = lean_unbox(v___x_839_);
v___x_4979__boxed_850_ = lean_unbox(v___x_840_);
v_res_851_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_4977__boxed_848_, v___x_4978__boxed_849_, v___x_4979__boxed_850_, v_x_841_, v_x_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_851_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(uint8_t v___x_853_, uint8_t v___x_854_, uint8_t v___x_855_, lean_object* v_x_856_, size_t v_x_857_, size_t v_x_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v_cs_865_; lean_object* v___x_866_; size_t v___x_867_; lean_object* v_j_868_; lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v_cs_865_ = lean_ctor_get(v_x_856_, 0);
lean_inc_ref(v_cs_865_);
lean_dec_ref_known(v_x_856_, 1);
v___x_866_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0);
v___x_867_ = lean_usize_shift_right(v_x_857_, v_x_858_);
v_j_868_ = lean_usize_to_nat(v___x_867_);
v___x_869_ = lean_array_get_borrowed(v___x_866_, v_cs_865_, v_j_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_shift_left(v___x_870_, v_x_858_);
v___x_872_ = lean_usize_sub(v___x_871_, v___x_870_);
v___x_873_ = lean_usize_land(v_x_857_, v___x_872_);
v___x_874_ = ((size_t)5ULL);
v___x_875_ = lean_usize_sub(v_x_858_, v___x_874_);
lean_inc(v___x_869_);
v___x_876_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_853_, v___x_854_, v___x_855_, v___x_869_, v___x_873_, v___x_875_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_j_868_, v___x_878_);
lean_dec(v_j_868_);
v___x_880_ = lean_array_get_size(v_cs_865_);
v___x_881_ = lean_nat_dec_lt(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v___x_879_);
lean_dec(v_a_877_);
lean_dec_ref(v_cs_865_);
return v___x_876_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_le(v___x_880_, v___x_880_);
if (v___x_882_ == 0)
{
if (v___x_881_ == 0)
{
lean_dec(v___x_879_);
lean_dec(v_a_877_);
lean_dec_ref(v_cs_865_);
return v___x_876_;
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
lean_dec_ref_known(v___x_876_, 1);
v___x_883_ = lean_usize_of_nat(v___x_879_);
lean_dec(v___x_879_);
v___x_884_ = lean_usize_of_nat(v___x_880_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_853_, v___x_854_, v___x_855_, v_cs_865_, v___x_883_, v___x_884_, v_a_877_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_cs_865_);
return v___x_885_;
}
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
lean_dec_ref_known(v___x_876_, 1);
v___x_886_ = lean_usize_of_nat(v___x_879_);
lean_dec(v___x_879_);
v___x_887_ = lean_usize_of_nat(v___x_880_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_853_, v___x_854_, v___x_855_, v_cs_865_, v___x_886_, v___x_887_, v_a_877_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_cs_865_);
return v___x_888_;
}
}
}
else
{
lean_dec(v_j_868_);
lean_dec_ref(v_cs_865_);
return v___x_876_;
}
}
else
{
lean_object* v_vs_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_909_; 
v_vs_889_ = lean_ctor_get(v_x_856_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_909_ == 0)
{
v___x_891_ = v_x_856_;
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_vs_889_);
lean_dec(v_x_856_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_usize_to_nat(v_x_857_);
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
lean_ctor_set(v___x_891_, 0, v_x_859_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_x_859_);
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
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_le(v___x_894_, v___x_894_);
if (v___x_899_ == 0)
{
if (v___x_895_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v___x_893_);
lean_dec_ref(v_vs_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v_x_859_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_x_859_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
lean_del_object(v___x_891_);
v___x_903_ = lean_usize_of_nat(v___x_893_);
lean_dec(v___x_893_);
v___x_904_ = lean_usize_of_nat(v___x_894_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_853_, v___x_854_, v___x_855_, v_vs_889_, v___x_903_, v___x_904_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_vs_889_);
return v___x_905_;
}
}
else
{
size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_891_);
v___x_906_ = lean_usize_of_nat(v___x_893_);
lean_dec(v___x_893_);
v___x_907_ = lean_usize_of_nat(v___x_894_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_853_, v___x_854_, v___x_855_, v_vs_889_, v___x_906_, v___x_907_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_vs_889_);
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v___x_5117__boxed_922_; uint8_t v___x_5118__boxed_923_; uint8_t v___x_5119__boxed_924_; size_t v_x_5121__boxed_925_; size_t v_x_5122__boxed_926_; lean_object* v_res_927_; 
v___x_5117__boxed_922_ = lean_unbox(v___x_910_);
v___x_5118__boxed_923_ = lean_unbox(v___x_911_);
v___x_5119__boxed_924_ = lean_unbox(v___x_912_);
v_x_5121__boxed_925_ = lean_unbox_usize(v_x_914_);
lean_dec(v_x_914_);
v_x_5122__boxed_926_ = lean_unbox_usize(v_x_915_);
lean_dec(v_x_915_);
v_res_927_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_5117__boxed_922_, v___x_5118__boxed_923_, v___x_5119__boxed_924_, v_x_913_, v_x_5121__boxed_925_, v_x_5122__boxed_926_, v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(uint8_t v___x_928_, uint8_t v___x_929_, uint8_t v___x_930_, lean_object* v_t_931_, lean_object* v_init_932_, lean_object* v_start_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_nat_dec_eq(v_start_933_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v_root_941_; lean_object* v_tail_942_; size_t v_shift_943_; lean_object* v_tailOff_944_; uint8_t v___x_945_; 
v_root_941_ = lean_ctor_get(v_t_931_, 0);
lean_inc_ref(v_root_941_);
v_tail_942_ = lean_ctor_get(v_t_931_, 1);
lean_inc_ref(v_tail_942_);
v_shift_943_ = lean_ctor_get_usize(v_t_931_, 4);
v_tailOff_944_ = lean_ctor_get(v_t_931_, 3);
lean_inc(v_tailOff_944_);
lean_dec_ref(v_t_931_);
v___x_945_ = lean_nat_dec_le(v_tailOff_944_, v_start_933_);
if (v___x_945_ == 0)
{
size_t v___x_946_; lean_object* v___x_947_; 
lean_dec(v_tailOff_944_);
v___x_946_ = lean_usize_of_nat(v_start_933_);
v___x_947_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_928_, v___x_929_, v___x_930_, v_root_941_, v___x_946_, v_shift_943_, v_init_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
v___x_949_ = lean_array_get_size(v_tail_942_);
v___x_950_ = lean_nat_dec_lt(v___x_939_, v___x_949_);
if (v___x_950_ == 0)
{
lean_dec(v_a_948_);
lean_dec_ref(v_tail_942_);
return v___x_947_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_le(v___x_949_, v___x_949_);
if (v___x_951_ == 0)
{
if (v___x_950_ == 0)
{
lean_dec(v_a_948_);
lean_dec_ref(v_tail_942_);
return v___x_947_;
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
lean_dec_ref_known(v___x_947_, 1);
v___x_952_ = ((size_t)0ULL);
v___x_953_ = lean_usize_of_nat(v___x_949_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_942_, v___x_952_, v___x_953_, v_a_948_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_942_);
return v___x_954_;
}
}
else
{
size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
lean_dec_ref_known(v___x_947_, 1);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = lean_usize_of_nat(v___x_949_);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_942_, v___x_955_, v___x_956_, v_a_948_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_942_);
return v___x_957_;
}
}
}
else
{
lean_dec_ref(v_tail_942_);
return v___x_947_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
lean_dec_ref(v_root_941_);
v___x_958_ = lean_nat_sub(v_start_933_, v_tailOff_944_);
lean_dec(v_tailOff_944_);
v___x_959_ = lean_array_get_size(v_tail_942_);
v___x_960_ = lean_nat_dec_lt(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec(v___x_958_);
lean_dec_ref(v_tail_942_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_init_932_);
return v___x_961_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_le(v___x_959_, v___x_959_);
if (v___x_962_ == 0)
{
if (v___x_960_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v___x_958_);
lean_dec_ref(v_tail_942_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_init_932_);
return v___x_963_;
}
else
{
size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_usize_of_nat(v___x_958_);
lean_dec(v___x_958_);
v___x_965_ = lean_usize_of_nat(v___x_959_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_942_, v___x_964_, v___x_965_, v_init_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_942_);
return v___x_966_;
}
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_usize_of_nat(v___x_958_);
lean_dec(v___x_958_);
v___x_968_ = lean_usize_of_nat(v___x_959_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_942_, v___x_967_, v___x_968_, v_init_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_942_);
return v___x_969_;
}
}
}
}
else
{
lean_object* v_root_970_; lean_object* v_tail_971_; lean_object* v___x_972_; 
v_root_970_ = lean_ctor_get(v_t_931_, 0);
lean_inc_ref(v_root_970_);
v_tail_971_ = lean_ctor_get(v_t_931_, 1);
lean_inc_ref(v_tail_971_);
lean_dec_ref(v_t_931_);
v___x_972_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_928_, v___x_929_, v___x_930_, v_root_970_, v_init_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
v___x_974_ = lean_array_get_size(v_tail_971_);
v___x_975_ = lean_nat_dec_lt(v___x_939_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec(v_a_973_);
lean_dec_ref(v_tail_971_);
return v___x_972_;
}
else
{
uint8_t v___x_976_; 
v___x_976_ = lean_nat_dec_le(v___x_974_, v___x_974_);
if (v___x_976_ == 0)
{
if (v___x_975_ == 0)
{
lean_dec(v_a_973_);
lean_dec_ref(v_tail_971_);
return v___x_972_;
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_974_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_971_, v___x_977_, v___x_978_, v_a_973_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_971_);
return v___x_979_;
}
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_974_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_928_, v___x_929_, v___x_930_, v_tail_971_, v___x_980_, v___x_981_, v_a_973_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_tail_971_);
return v___x_982_;
}
}
}
else
{
lean_dec_ref(v_tail_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v_t_986_, lean_object* v_init_987_, lean_object* v_start_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v___x_5243__boxed_994_; uint8_t v___x_5244__boxed_995_; uint8_t v___x_5245__boxed_996_; lean_object* v_res_997_; 
v___x_5243__boxed_994_ = lean_unbox(v___x_983_);
v___x_5244__boxed_995_ = lean_unbox(v___x_984_);
v___x_5245__boxed_996_ = lean_unbox(v___x_985_);
v_res_997_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_5243__boxed_994_, v___x_5244__boxed_995_, v___x_5245__boxed_996_, v_t_986_, v_init_987_, v_start_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v_start_988_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(uint8_t v___x_998_, uint8_t v___x_999_, uint8_t v___x_1000_, lean_object* v_lctx_1001_, lean_object* v_init_1002_, lean_object* v_start_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_decls_1009_; lean_object* v___x_1010_; 
v_decls_1009_ = lean_ctor_get(v_lctx_1001_, 1);
lean_inc_ref(v_decls_1009_);
lean_dec_ref(v_lctx_1001_);
v___x_1010_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_998_, v___x_999_, v___x_1000_, v_decls_1009_, v_init_1002_, v_start_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_lctx_1014_, lean_object* v_init_1015_, lean_object* v_start_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_5345__boxed_1022_; uint8_t v___x_5346__boxed_1023_; uint8_t v___x_5347__boxed_1024_; lean_object* v_res_1025_; 
v___x_5345__boxed_1022_ = lean_unbox(v___x_1011_);
v___x_5346__boxed_1023_ = lean_unbox(v___x_1012_);
v___x_5347__boxed_1024_ = lean_unbox(v___x_1013_);
v_res_1025_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_5345__boxed_1022_, v___x_5346__boxed_1023_, v___x_5347__boxed_1024_, v_lctx_1014_, v_init_1015_, v_start_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v_start_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(uint8_t v___x_1029_, uint8_t v___x_1030_, uint8_t v___x_1031_, lean_object* v_fst_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_type_1036_, lean_object* v_val_1037_, lean_object* v_userName_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(v___x_1029_, v___x_1030_, v___x_1031_, v_fst_1032_, v___x_1033_, v___x_1034_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v_snd_1046_; lean_object* v_fst_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1104_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v_snd_1046_ = lean_ctor_get(v_a_1045_, 1);
v_fst_1047_ = lean_ctor_get(v_a_1045_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_a_1045_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1049_ = v_a_1045_;
v_isShared_1050_ = v_isSharedCheck_1104_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1047_);
lean_dec(v_a_1045_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1104_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1103_; 
v_fst_1051_ = lean_ctor_get(v_snd_1046_, 0);
v_snd_1052_ = lean_ctor_get(v_snd_1046_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_snd_1046_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1054_ = v_snd_1046_;
v_isShared_1055_ = v_isSharedCheck_1103_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_snd_1046_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1103_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; 
lean_inc(v___x_1035_);
v___x_1056_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(v___x_1035_, v_fst_1047_, v_fst_1051_, v_snd_1052_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1102_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1102_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1102_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1101_; 
v___x_1061_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1036_, v___y_1040_);
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Meta_ppExpr(v_a_1062_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1100_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1100_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1100_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_1057_);
v___x_1072_ = l_Lean_Meta_getGoalPrefix(v_val_1037_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 3);
lean_ctor_set(v___x_1064_, 0, v___x_1072_);
v___x_1074_ = v___x_1064_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 5);
lean_ctor_set(v___x_1054_, 1, v___x_1074_);
lean_ctor_set(v___x_1054_, 0, v___x_1071_);
v___x_1076_ = v___x_1054_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 4);
lean_ctor_set(v___x_1049_, 1, v_a_1067_);
lean_ctor_set(v___x_1049_, 0, v___x_1035_);
v___x_1078_ = v___x_1049_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1067_);
v___x_1078_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
if (lean_obj_tag(v_userName_1038_) == 0)
{
lean_object* v___x_1081_; 
lean_del_object(v___x_1059_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1079_);
v___x_1081_ = v___x_1069_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1083_ = ((lean_object*)(l_Lean_Meta_ppGoal___lam__0___closed__1));
v___x_1084_ = l_Lean_Name_eraseMacroScopes(v_userName_1038_);
v___x_1085_ = 1;
v___x_1086_ = l_Lean_Name_toString(v___x_1084_, v___x_1085_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 3);
lean_ctor_set(v___x_1059_, 0, v___x_1086_);
v___x_1088_ = v___x_1059_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1083_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1));
v___x_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1079_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1092_);
v___x_1094_ = v___x_1069_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
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
lean_del_object(v___x_1064_);
lean_del_object(v___x_1059_);
lean_dec(v_a_1057_);
lean_del_object(v___x_1054_);
lean_del_object(v___x_1049_);
lean_dec(v___x_1035_);
return v___x_1066_;
}
}
}
}
else
{
lean_del_object(v___x_1054_);
lean_del_object(v___x_1049_);
lean_dec_ref(v_type_1036_);
lean_dec(v___x_1035_);
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_type_1036_);
lean_dec(v___x_1035_);
v_a_1105_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1044_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1044_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v___x_1115_, lean_object* v_fst_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_type_1120_, lean_object* v_val_1121_, lean_object* v_userName_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_5380__boxed_1128_; uint8_t v___x_5381__boxed_1129_; uint8_t v___x_5382__boxed_1130_; lean_object* v_res_1131_; 
v___x_5380__boxed_1128_ = lean_unbox(v___x_1113_);
v___x_5381__boxed_1129_ = lean_unbox(v___x_1114_);
v___x_5382__boxed_1130_ = lean_unbox(v___x_1115_);
v_res_1131_ = l_Lean_Meta_ppGoal___lam__0(v___x_5380__boxed_1128_, v___x_5381__boxed_1129_, v___x_5382__boxed_1130_, v_fst_1116_, v___x_1117_, v___x_1118_, v___x_1119_, v_type_1120_, v_val_1121_, v_userName_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v_userName_1122_);
lean_dec_ref(v_val_1121_);
lean_dec(v___x_1118_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object* v_mvarId_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v_mctx_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_st_ref_get(v_a_1143_);
v_mctx_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_mctx_1148_);
lean_dec(v___x_1147_);
v___x_1149_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1148_, v_mvarId_1141_);
lean_dec_ref(v_mctx_1148_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__1));
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v_val_1152_; lean_object* v_options_1153_; lean_object* v_userName_1154_; lean_object* v_lctx_1155_; lean_object* v_type_1156_; lean_object* v_localInstances_1157_; uint8_t v_kind_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_fst_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_val_1152_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1149_, 1);
v_options_1153_ = lean_ctor_get(v_a_1144_, 2);
v_userName_1154_ = lean_ctor_get(v_val_1152_, 0);
lean_inc(v_userName_1154_);
v_lctx_1155_ = lean_ctor_get(v_val_1152_, 1);
v_type_1156_ = lean_ctor_get(v_val_1152_, 2);
lean_inc_ref(v_type_1156_);
v_localInstances_1157_ = lean_ctor_get(v_val_1152_, 4);
lean_inc_ref(v_localInstances_1157_);
v_kind_1158_ = lean_ctor_get_uint8(v_val_1152_, sizeof(void*)*7);
v___x_1159_ = l_Lean_Meta_pp_auxDecls;
v___x_1160_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1153_, v___x_1159_);
v___x_1161_ = l_Lean_Meta_pp_implementationDetailHyps;
v___x_1162_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(v_options_1153_, v___x_1161_);
v___x_1163_ = lean_box(1);
lean_inc_ref(v_options_1153_);
v___x_1164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1164_, 0, v_options_1153_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
lean_inc_ref(v_lctx_1155_);
v___x_1165_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1155_, v___x_1164_);
v_fst_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_n(v_fst_1166_, 2);
lean_dec_ref(v___x_1165_);
v___x_1167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
v___x_1168_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_1158_);
v___x_1169_ = ((lean_object*)(l_Lean_Meta_ppGoal___closed__3));
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_box(v___x_1168_);
v___x_1172_ = lean_box(v___x_1162_);
v___x_1173_ = lean_box(v___x_1160_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1174_, 0, v___x_1171_);
lean_closure_set(v___f_1174_, 1, v___x_1172_);
lean_closure_set(v___f_1174_, 2, v___x_1173_);
lean_closure_set(v___f_1174_, 3, v_fst_1166_);
lean_closure_set(v___f_1174_, 4, v___x_1169_);
lean_closure_set(v___f_1174_, 5, v___x_1170_);
lean_closure_set(v___f_1174_, 6, v___x_1167_);
lean_closure_set(v___f_1174_, 7, v_type_1156_);
lean_closure_set(v___f_1174_, 8, v_val_1152_);
lean_closure_set(v___f_1174_, 9, v_userName_1154_);
v___x_1175_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(v_fst_1166_, v_localInstances_1157_, v___f_1174_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object* v_mvarId_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_ppGoal(v_mvarId_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_mvarId_1176_);
return v_res_1182_;
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
