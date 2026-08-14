// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.EPost
// Imports: public import Lean.Meta.Sym public import Std.WP public import Lean.Meta.Tactic.Replace
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 91, 36, 233, 42, 127, 239, 103)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 138, 171, 54, 136, 21, 182, 106)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value_aux_3),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 202, 160, 142, 136, 225, 216, 6)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tail"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 91, 36, 233, 42, 127, 239, 103)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 138, 171, 54, 136, 21, 182, 106)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 110, 24, 232, 154, 190, 182, 240)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_peelEPostTailChain(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bot_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 109, 99, 66, 8, 241, 194, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "head_bot"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 91, 36, 233, 42, 127, 239, 103)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 138, 171, 54, 136, 21, 182, 106)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 168, 162, 216, 128, 141, 125, 155)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg(lean_object* v_range_14_, lean_object* v_b_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_stop_18_; lean_object* v_step_19_; uint8_t v___x_20_; 
v_stop_18_ = lean_ctor_get(v_range_14_, 1);
v_step_19_ = lean_ctor_get(v_range_14_, 2);
v___x_20_ = lean_nat_dec_lt(v_i_16_, v_stop_18_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v_i_16_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v_b_15_);
return v___x_21_;
}
else
{
lean_object* v_snd_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_48_; 
v_snd_22_ = lean_ctor_get(v_b_15_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_b_15_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v_b_15_, 0);
lean_dec(v_unused_49_);
v___x_24_ = v_b_15_;
v_isShared_25_ = v_isSharedCheck_48_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_snd_22_);
lean_dec(v_b_15_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_48_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_snd_22_);
v___x_32_ = l_Lean_Expr_cleanupAnnotations(v_snd_22_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v___x_32_);
lean_dec(v_i_16_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_arg_34_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_arg_34_);
v___x_35_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
lean_dec_ref(v_arg_34_);
lean_dec(v_i_16_);
goto v___jp_26_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_34_);
lean_dec(v_i_16_);
goto v___jp_26_;
}
else
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_40_ = l_Lean_Expr_isApp(v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v___x_39_);
lean_dec_ref(v_arg_34_);
lean_dec(v_i_16_);
goto v___jp_26_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_39_);
v___x_42_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6));
v___x_43_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_42_);
lean_dec_ref(v___x_41_);
if (v___x_43_ == 0)
{
lean_dec_ref(v_arg_34_);
lean_dec(v_i_16_);
goto v___jp_26_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_del_object(v___x_24_);
lean_dec(v_snd_22_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v_arg_34_);
v___x_46_ = lean_nat_add(v_i_16_, v_step_19_);
lean_dec(v_i_16_);
v_b_15_ = v___x_45_;
v_i_16_ = v___x_46_;
goto _start;
}
}
}
}
}
v___jp_26_:
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0));
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_27_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_snd_22_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___boxed(lean_object* v_range_50_, lean_object* v_b_51_, lean_object* v_i_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg(v_range_50_, v_b_51_, v_i_52_);
lean_dec_ref(v_range_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex(lean_object* v_target_55_, lean_object* v_index_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_99_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v_index_56_);
lean_ctor_set(v___x_69_, 2, v___x_68_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_target_55_);
v___x_72_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg(v___x_69_, v___x_71_, v___x_67_);
lean_dec_ref_known(v___x_69_, 3);
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_99_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_99_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_99_;
goto v_resetjp_74_;
}
v___jp_64_:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
v_resetjp_74_:
{
lean_object* v_fst_77_; 
v_fst_77_ = lean_ctor_get(v_a_73_, 0);
if (lean_obj_tag(v_fst_77_) == 0)
{
lean_object* v_snd_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_snd_78_ = lean_ctor_get(v_a_73_, 1);
lean_inc(v_snd_78_);
lean_dec(v_a_73_);
v___x_79_ = l_Lean_Expr_cleanupAnnotations(v_snd_78_);
v___x_80_ = l_Lean_Expr_isApp(v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v___x_79_);
lean_del_object(v___x_75_);
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = l_Lean_Expr_appFnCleanup___redArg(v___x_79_);
v___x_82_ = l_Lean_Expr_isApp(v___x_81_);
if (v___x_82_ == 0)
{
lean_dec_ref(v___x_81_);
lean_del_object(v___x_75_);
goto v___jp_64_;
}
else
{
lean_object* v_arg_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_arg_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc_ref(v_arg_83_);
v___x_84_ = l_Lean_Expr_appFnCleanup___redArg(v___x_81_);
v___x_85_ = l_Lean_Expr_isApp(v___x_84_);
if (v___x_85_ == 0)
{
lean_dec_ref(v___x_84_);
lean_dec_ref(v_arg_83_);
lean_del_object(v___x_75_);
goto v___jp_64_;
}
else
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = l_Lean_Expr_appFnCleanup___redArg(v___x_84_);
v___x_87_ = l_Lean_Expr_isApp(v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v___x_86_);
lean_dec_ref(v_arg_83_);
lean_del_object(v___x_75_);
goto v___jp_64_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_86_);
v___x_89_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6));
v___x_90_ = l_Lean_Expr_isConstOf(v___x_88_, v___x_89_);
lean_dec_ref(v___x_88_);
if (v___x_90_ == 0)
{
lean_dec_ref(v_arg_83_);
lean_del_object(v___x_75_);
goto v___jp_64_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_arg_83_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_91_);
v___x_93_ = v___x_75_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_95_; lean_object* v___x_97_; 
lean_inc_ref(v_fst_77_);
lean_dec(v_a_73_);
v_val_95_ = lean_ctor_get(v_fst_77_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v_fst_77_, 1);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v_val_95_);
v___x_97_ = v___x_75_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex___boxed(lean_object* v_target_100_, lean_object* v_index_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex(v_target_100_, v_index_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0(lean_object* v_range_110_, lean_object* v_b_111_, lean_object* v_i_112_, lean_object* v_hs_113_, lean_object* v_hl_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___redArg(v_range_110_, v_b_111_, v_i_112_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0___boxed(lean_object* v_range_123_, lean_object* v_b_124_, lean_object* v_i_125_, lean_object* v_hs_126_, lean_object* v_hl_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_mkEPostAtIndex_spec__0(v_range_123_, v_b_124_, v_i_125_, v_hs_126_, v_hl_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec_ref(v_range_123_);
return v_res_135_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v_dummy_137_; 
v___x_136_ = lean_box(0);
v_dummy_137_ = l_Lean_Expr_sort___override(v___x_136_);
return v_dummy_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0(lean_object* v_curr_145_, lean_object* v_idx_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v___y_151_; 
if (lean_obj_tag(v_x_147_) == 5)
{
lean_object* v_fn_160_; lean_object* v_arg_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_fn_160_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_fn_160_);
v_arg_161_ = lean_ctor_get(v_x_147_, 1);
lean_inc_ref(v_arg_161_);
lean_dec_ref_known(v_x_147_, 2);
v___x_162_ = lean_array_set(v_x_148_, v_x_149_, v_arg_161_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_sub(v_x_149_, v___x_163_);
lean_dec(v_x_149_);
v_x_147_ = v_fn_160_;
v_x_148_ = v___x_162_;
v_x_149_ = v___x_164_;
goto _start;
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; 
lean_dec(v_x_149_);
v___x_166_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0___closed__1));
v___x_167_ = l_Lean_Expr_isConstOf(v_x_147_, v___x_166_);
lean_dec_ref(v_x_147_);
if (v___x_167_ == 0)
{
v___y_151_ = v___x_167_;
goto v___jp_150_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_array_get_size(v_x_148_);
v___x_170_ = lean_nat_dec_lt(v___x_168_, v___x_169_);
v___y_151_ = v___x_170_;
goto v___jp_150_;
}
}
v___jp_150_:
{
if (v___y_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec_ref(v_x_148_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_curr_145_);
lean_ctor_set(v___x_152_, 1, v_idx_146_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec_ref(v_curr_145_);
v___x_153_ = l_Lean_instInhabitedExpr;
v___x_154_ = lean_array_get_size(v_x_148_);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_array_get(v___x_153_, v_x_148_, v___x_156_);
lean_dec(v___x_156_);
lean_dec_ref(v_x_148_);
v___x_158_ = lean_nat_add(v_idx_146_, v___x_155_);
lean_dec(v_idx_146_);
v___x_159_ = l_Lean_Elab_Tactic_VCGen_peelEPostTailChain(v___x_157_, v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_peelEPostTailChain(lean_object* v_curr_171_, lean_object* v_idx_172_){
_start:
{
lean_object* v___x_173_; lean_object* v_dummy_174_; lean_object* v_nargs_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_173_ = l_Lean_Expr_consumeMData(v_curr_171_);
v_dummy_174_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0, &l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0);
v_nargs_175_ = l_Lean_Expr_getAppNumArgs(v___x_173_);
lean_inc(v_nargs_175_);
v___x_176_ = lean_mk_array(v_nargs_175_, v_dummy_174_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_sub(v_nargs_175_, v___x_177_);
lean_dec(v_nargs_175_);
v___x_179_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_peelEPostTailChain_spec__0(v_curr_171_, v_idx_172_, v___x_173_, v___x_176_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object* v_tail_207_, lean_object* v_as_208_, size_t v_sz_209_, size_t v_i_210_, lean_object* v_b_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_lt(v_i_210_, v_sz_209_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec(v_tail_207_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_b_211_);
return v___x_220_;
}
else
{
lean_object* v_snd_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_467_; 
v_snd_221_ = lean_ctor_get(v_b_211_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_b_211_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v_b_211_, 0);
lean_dec(v_unused_468_);
v___x_223_ = v_b_211_;
v_isShared_224_ = v_isSharedCheck_467_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snd_221_);
lean_dec(v_b_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_467_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_snd_225_; lean_object* v_snd_226_; lean_object* v_snd_227_; lean_object* v_fst_228_; 
v_snd_225_ = lean_ctor_get(v_snd_221_, 1);
lean_inc(v_snd_225_);
v_snd_226_ = lean_ctor_get(v_snd_225_, 1);
lean_inc(v_snd_226_);
v_snd_227_ = lean_ctor_get(v_snd_226_, 1);
lean_inc(v_snd_227_);
v_fst_228_ = lean_ctor_get(v_snd_227_, 0);
lean_inc(v_fst_228_);
if (lean_obj_tag(v_fst_228_) == 7)
{
lean_object* v_fst_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_424_; 
v_fst_229_ = lean_ctor_get(v_snd_221_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_snd_221_, 1);
lean_dec(v_unused_425_);
v___x_231_ = v_snd_221_;
v_isShared_232_ = v_isSharedCheck_424_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_fst_229_);
lean_dec(v_snd_221_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_424_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fst_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_422_; 
v_fst_233_ = lean_ctor_get(v_snd_225_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_snd_225_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_snd_225_, 1);
lean_dec(v_unused_423_);
v___x_235_ = v_snd_225_;
v_isShared_236_ = v_isSharedCheck_422_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_fst_233_);
lean_dec(v_snd_225_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_422_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_fst_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_420_; 
v_fst_237_ = lean_ctor_get(v_snd_226_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_snd_226_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_snd_226_, 1);
lean_dec(v_unused_421_);
v___x_239_ = v_snd_226_;
v_isShared_240_ = v_isSharedCheck_420_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_fst_237_);
lean_dec(v_snd_226_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_420_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_snd_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_418_; 
v_snd_241_ = lean_ctor_get(v_snd_227_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_snd_227_, 0);
lean_dec(v_unused_419_);
v___x_243_ = v_snd_227_;
v_isShared_244_ = v_isSharedCheck_418_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snd_241_);
lean_dec(v_snd_227_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_418_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_binderType_245_; lean_object* v_body_246_; uint8_t v___x_247_; 
v_binderType_245_ = lean_ctor_get(v_fst_228_, 1);
v_body_246_ = lean_ctor_get(v_fst_228_, 2);
v___x_247_ = l_Lean_Expr_hasLooseBVars(v_body_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3));
v___x_249_ = l_Lean_Expr_isAppOf(v_snd_241_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec(v_tail_207_);
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_244_ == 0)
{
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_snd_241_);
v___x_252_ = v_reuseFailAlloc_266_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_252_);
v___x_254_ = v___x_239_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_265_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_254_);
v___x_256_ = v___x_235_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_264_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_256_);
v___x_258_ = v___x_231_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_258_);
lean_ctor_set(v___x_223_, 0, v___x_250_);
v___x_260_ = v___x_223_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
}
}
}
}
else
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Expr_appArg_x21(v_snd_241_);
if (lean_obj_tag(v___x_267_) == 6)
{
lean_object* v_body_268_; lean_object* v___x_269_; 
v_body_268_ = lean_ctor_get(v___x_267_, 2);
lean_inc_ref(v_body_268_);
lean_dec_ref_known(v___x_267_, 3);
lean_inc_ref(v_binderType_245_);
v___x_269_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_245_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
lean_inc_ref(v_body_246_);
v___x_271_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_246_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
lean_inc(v_a_270_);
v___x_273_ = l_Lean_Meta_decLevel(v_a_270_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
lean_inc(v_a_272_);
v___x_275_ = l_Lean_Meta_decLevel(v_a_272_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v_a_277_ = lean_array_uget_borrowed(v_as_208_, v_i_210_);
v___x_278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6));
lean_inc(v_tail_207_);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_a_276_);
lean_ctor_set(v___x_279_, 1, v_tail_207_);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v_a_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_mkConst(v___x_278_, v___x_280_);
lean_inc(v_a_277_);
lean_inc_ref(v_body_268_);
lean_inc_ref(v_body_246_);
lean_inc_ref(v_binderType_245_);
v___x_282_ = l_Lean_mkApp4(v___x_281_, v_binderType_245_, v_body_246_, v_body_268_, v_a_277_);
lean_inc_ref(v___x_282_);
v___x_283_ = l_Lean_Meta_Sym_inferType(v___x_282_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_343_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_343_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_343_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_343_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8));
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = l_Lean_Expr_isAppOfArity(v_a_284_, v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec(v_a_284_);
lean_dec_ref(v___x_282_);
lean_dec(v_a_272_);
lean_dec(v_a_270_);
lean_dec_ref(v_body_268_);
lean_dec(v_tail_207_);
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_244_ == 0)
{
v___x_293_ = v___x_243_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_snd_241_);
v___x_293_ = v_reuseFailAlloc_309_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_293_);
v___x_295_ = v___x_239_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_308_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_295_);
v___x_297_ = v___x_235_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_307_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_297_);
v___x_299_ = v___x_231_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_306_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_299_);
lean_ctor_set(v___x_223_, 0, v___x_291_);
v___x_301_ = v___x_223_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_301_);
v___x_303_ = v___x_286_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
lean_inc_ref_n(v_body_246_, 3);
lean_inc_ref_n(v_binderType_245_, 2);
lean_del_object(v___x_286_);
lean_dec(v_snd_241_);
lean_dec_ref_known(v_fst_228_, 3);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_Expr_appArg_x21(v_a_284_);
lean_dec(v_a_284_);
v___x_312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10));
lean_inc(v_tail_207_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v_a_272_);
lean_ctor_set(v___x_313_, 1, v_tail_207_);
lean_inc_ref(v___x_313_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_a_270_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_mkConst(v___x_312_, v___x_314_);
v___x_316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12));
v___x_317_ = 0;
v___x_318_ = l_Lean_Expr_lam___override(v___x_316_, v_binderType_245_, v_body_246_, v___x_317_);
lean_inc_n(v_a_277_, 3);
lean_inc(v_fst_237_);
lean_inc(v_fst_233_);
v___x_319_ = l_Lean_mkApp6(v___x_315_, v_binderType_245_, v___x_318_, v_fst_233_, v_fst_237_, v_fst_229_, v_a_277_);
v___x_320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14));
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_313_);
v___x_322_ = l_Lean_Expr_app___override(v_fst_233_, v_a_277_);
v___x_323_ = l_Lean_Expr_app___override(v_fst_237_, v_a_277_);
lean_inc_ref(v___x_311_);
lean_inc_ref(v___x_322_);
v___x_324_ = l_Lean_mkApp6(v___x_321_, v_body_246_, v___x_322_, v___x_323_, v___x_311_, v___x_319_, v___x_282_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_body_268_);
lean_ctor_set(v___x_243_, 0, v_body_246_);
v___x_326_ = v___x_243_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_body_246_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_body_268_);
v___x_326_ = v_reuseFailAlloc_342_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_326_);
lean_ctor_set(v___x_239_, 0, v___x_311_);
v___x_328_ = v___x_239_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_341_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_328_);
lean_ctor_set(v___x_235_, 0, v___x_322_);
v___x_330_ = v___x_235_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_340_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_330_);
lean_ctor_set(v___x_231_, 0, v___x_324_);
v___x_332_ = v___x_231_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_339_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_332_);
lean_ctor_set(v___x_223_, 0, v___x_310_);
v___x_334_ = v___x_223_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
size_t v___x_335_; size_t v___x_336_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_210_, v___x_335_);
v_i_210_ = v___x_336_;
v_b_211_ = v___x_334_;
goto _start;
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
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v___x_282_);
lean_dec(v_a_272_);
lean_dec(v_a_270_);
lean_dec_ref(v_body_268_);
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_del_object(v___x_235_);
lean_dec(v_fst_233_);
lean_del_object(v___x_231_);
lean_dec(v_fst_229_);
lean_dec_ref_known(v_fst_228_, 3);
lean_del_object(v___x_223_);
lean_dec(v_tail_207_);
v_a_344_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_283_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_283_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_274_);
lean_dec(v_a_272_);
lean_dec(v_a_270_);
lean_dec_ref(v_body_268_);
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_del_object(v___x_235_);
lean_dec(v_fst_233_);
lean_del_object(v___x_231_);
lean_dec(v_fst_229_);
lean_dec_ref_known(v_fst_228_, 3);
lean_del_object(v___x_223_);
lean_dec(v_tail_207_);
v_a_352_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_275_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_275_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_a_272_);
lean_dec(v_a_270_);
lean_dec_ref(v_body_268_);
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_del_object(v___x_235_);
lean_dec(v_fst_233_);
lean_del_object(v___x_231_);
lean_dec(v_fst_229_);
lean_dec_ref_known(v_fst_228_, 3);
lean_del_object(v___x_223_);
lean_dec(v_tail_207_);
v_a_360_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_273_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_273_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_a_270_);
lean_dec_ref(v_body_268_);
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_del_object(v___x_235_);
lean_dec(v_fst_233_);
lean_del_object(v___x_231_);
lean_dec(v_fst_229_);
lean_dec_ref_known(v_fst_228_, 3);
lean_del_object(v___x_223_);
lean_dec(v_tail_207_);
v_a_368_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_271_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_271_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_body_268_);
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_del_object(v___x_239_);
lean_dec(v_fst_237_);
lean_del_object(v___x_235_);
lean_dec(v_fst_233_);
lean_del_object(v___x_231_);
lean_dec(v_fst_229_);
lean_dec_ref_known(v_fst_228_, 3);
lean_del_object(v___x_223_);
lean_dec(v_tail_207_);
v_a_376_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_269_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_269_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec_ref(v___x_267_);
lean_dec(v_tail_207_);
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_244_ == 0)
{
v___x_386_ = v___x_243_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_snd_241_);
v___x_386_ = v_reuseFailAlloc_400_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_386_);
v___x_388_ = v___x_239_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_399_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_388_);
v___x_390_ = v___x_235_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_398_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_390_);
v___x_392_ = v___x_231_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_397_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_392_);
lean_ctor_set(v___x_223_, 0, v___x_384_);
v___x_394_ = v___x_223_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
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
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec(v_tail_207_);
v___x_401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_244_ == 0)
{
v___x_403_ = v___x_243_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_241_);
v___x_403_ = v_reuseFailAlloc_417_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_403_);
v___x_405_ = v___x_239_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_416_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_405_);
v___x_407_ = v___x_235_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_415_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_407_);
v___x_409_ = v___x_231_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_414_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_409_);
lean_ctor_set(v___x_223_, 0, v___x_401_);
v___x_411_ = v___x_223_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
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
lean_object* v_fst_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_tail_207_);
v_fst_426_ = lean_ctor_get(v_snd_221_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_snd_221_, 1);
lean_dec(v_unused_466_);
v___x_428_ = v_snd_221_;
v_isShared_429_ = v_isSharedCheck_465_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_fst_426_);
lean_dec(v_snd_221_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_465_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fst_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_463_; 
v_fst_430_ = lean_ctor_get(v_snd_225_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_snd_225_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_snd_225_, 1);
lean_dec(v_unused_464_);
v___x_432_ = v_snd_225_;
v_isShared_433_ = v_isSharedCheck_463_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_fst_430_);
lean_dec(v_snd_225_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_463_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_fst_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_461_; 
v_fst_434_ = lean_ctor_get(v_snd_226_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_snd_226_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_snd_226_, 1);
lean_dec(v_unused_462_);
v___x_436_ = v_snd_226_;
v_isShared_437_ = v_isSharedCheck_461_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_fst_434_);
lean_dec(v_snd_226_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_461_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_459_; 
v_snd_438_ = lean_ctor_get(v_snd_227_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_snd_227_, 0);
lean_dec(v_unused_460_);
v___x_440_ = v_snd_227_;
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_dec(v_snd_227_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_441_ == 0)
{
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_snd_438_);
v___x_444_ = v_reuseFailAlloc_458_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_444_);
v___x_446_ = v___x_436_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_457_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_446_);
v___x_448_ = v___x_432_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_456_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_448_);
v___x_450_ = v___x_428_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_455_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_450_);
lean_ctor_set(v___x_223_, 0, v___x_442_);
v___x_452_ = v___x_223_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object* v_tail_469_, lean_object* v_as_470_, lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_482_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0(v_tail_469_, v_as_470_, v_sz_boxed_481_, v_i_boxed_482_, v_b_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec_ref(v_as_470_);
return v_res_483_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_Level_succ___override(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_mkSort(v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f(lean_object* v_goal_503_, lean_object* v_target_504_, lean_object* v_head_505_, lean_object* v_args_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_array_get_size(v_args_506_);
v___x_522_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_dec_lt(v___x_525_, v___x_521_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(2u);
v___x_530_ = lean_nat_dec_lt(v___x_529_, v___x_521_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_array_fget_borrowed(v_args_506_, v___x_529_);
lean_inc(v___x_533_);
v___x_534_ = l_Lean_Expr_cleanupAnnotations(v___x_533_);
v___x_535_ = l_Lean_Expr_isApp(v___x_534_);
if (v___x_535_ == 0)
{
lean_dec_ref(v___x_534_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_514_;
}
else
{
lean_object* v_arg_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_arg_536_ = lean_ctor_get(v___x_534_, 1);
lean_inc_ref(v_arg_536_);
v___x_537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_534_);
v___x_538_ = l_Lean_Expr_isApp(v___x_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v___x_537_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_514_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_537_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__1));
v___x_541_ = l_Lean_Expr_isConstOf(v___x_539_, v___x_540_);
lean_dec_ref(v___x_539_);
if (v___x_541_ == 0)
{
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_514_;
}
else
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Expr_isApp(v_arg_536_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v_dummy_546_; lean_object* v_nargs_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_clArgs_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_545_ = l_Lean_Expr_appArg_x21(v_arg_536_);
lean_dec_ref(v_arg_536_);
v_dummy_546_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0, &l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_peelEPostTailChain___closed__0);
v_nargs_547_ = l_Lean_Expr_getAppNumArgs(v___x_545_);
lean_inc(v_nargs_547_);
v___x_548_ = lean_mk_array(v_nargs_547_, v_dummy_546_);
v___x_549_ = lean_nat_sub(v_nargs_547_, v___x_525_);
lean_dec(v_nargs_547_);
v_clArgs_550_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_545_, v___x_548_, v___x_549_);
v___x_551_ = lean_array_get_size(v_clArgs_550_);
v___x_552_ = lean_nat_dec_le(v___x_529_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v_clArgs_550_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Expr_constLevels_x21(v_head_505_);
if (lean_obj_tag(v___x_555_) == 1)
{
lean_object* v_tail_556_; 
v_tail_556_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_tail_556_);
if (lean_obj_tag(v_tail_556_) == 1)
{
lean_object* v_tail_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_695_; 
v_tail_557_ = lean_ctor_get(v_tail_556_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_tail_556_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_tail_556_, 0);
lean_dec(v_unused_696_);
v___x_559_ = v_tail_556_;
v_isShared_560_ = v_isSharedCheck_695_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_tail_557_);
lean_dec(v_tail_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_695_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
if (lean_obj_tag(v_tail_557_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_curCL_565_; lean_object* v___x_566_; lean_object* v_ctInst_567_; lean_object* v_curHead_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_acc_571_; lean_object* v___x_572_; 
v___x_561_ = l_Lean_instInhabitedExpr;
v___x_562_ = lean_array_fget_borrowed(v_args_506_, v___x_520_);
v___x_563_ = lean_array_fget_borrowed(v_args_506_, v___x_525_);
v___x_564_ = lean_nat_sub(v___x_551_, v___x_529_);
v_curCL_565_ = lean_array_get(v___x_561_, v_clArgs_550_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = lean_nat_sub(v___x_551_, v___x_525_);
v_ctInst_567_ = lean_array_get(v___x_561_, v_clArgs_550_, v___x_566_);
lean_dec(v___x_566_);
lean_dec_ref(v_clArgs_550_);
lean_inc(v___x_533_);
lean_inc_n(v___x_563_, 2);
lean_inc_n(v___x_562_, 2);
lean_inc_ref(v_head_505_);
v_curHead_568_ = l_Lean_mkApp3(v_head_505_, v___x_562_, v___x_563_, v___x_533_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__3));
v___x_570_ = l_Lean_mkConst(v___x_569_, v___x_555_);
lean_inc(v_curCL_565_);
v_acc_571_ = l_Lean_mkApp4(v___x_570_, v___x_562_, v___x_563_, v_curCL_565_, v_ctInst_567_);
lean_inc_ref(v_acc_571_);
v___x_572_ = l_Lean_Meta_Sym_inferType(v_acc_571_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_686_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_686_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_686_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_686_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8));
v___x_578_ = lean_unsigned_to_nat(3u);
v___x_579_ = l_Lean_Expr_isAppOfArity(v_a_573_, v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_a_573_);
lean_dec_ref(v_acc_571_);
lean_dec_ref(v_curHead_568_);
lean_dec(v_curCL_565_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v___x_580_ = lean_box(0);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_580_);
v___x_582_ = v___x_575_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; size_t v_sz_592_; size_t v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_575_);
v___x_584_ = l_Lean_Expr_appArg_x21(v_a_573_);
lean_dec(v_a_573_);
v___x_585_ = l_Array_extract___redArg(v_args_506_, v___x_578_, v___x_521_);
v___x_586_ = lean_box(0);
lean_inc(v___x_562_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_562_);
lean_ctor_set(v___x_587_, 1, v_curCL_565_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_584_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_curHead_568_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_acc_571_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_586_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v_sz_592_ = lean_array_size(v___x_585_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f_spec__0(v_tail_557_, v___x_585_, v_sz_592_, v___x_593_, v___x_591_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec_ref(v___x_585_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_677_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_677_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_677_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_677_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_fst_599_; 
v_fst_599_ = lean_ctor_get(v_a_595_, 0);
if (lean_obj_tag(v_fst_599_) == 0)
{
lean_object* v_snd_600_; lean_object* v_nargs_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_snd_600_ = lean_ctor_get(v_a_595_, 1);
lean_inc(v_snd_600_);
lean_dec(v_a_595_);
v_nargs_601_ = l_Lean_Expr_getAppNumArgs(v_target_504_);
lean_inc(v_nargs_601_);
v___x_602_ = lean_mk_array(v_nargs_601_, v_dummy_546_);
v___x_603_ = lean_nat_sub(v_nargs_601_, v___x_525_);
lean_dec(v_nargs_601_);
lean_inc_ref(v_target_504_);
v___x_604_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_504_, v___x_602_, v___x_603_);
v___x_605_ = lean_array_get_size(v___x_604_);
v___x_606_ = lean_nat_dec_lt(v___x_520_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v___x_604_);
lean_dec(v_snd_600_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_586_);
v___x_608_ = v___x_597_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_586_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_lt(v___x_525_, v___x_605_);
if (v___x_610_ == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v___x_604_);
lean_dec(v_snd_600_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_586_);
v___x_612_ = v___x_597_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_586_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_lt(v___x_529_, v___x_605_);
if (v___x_614_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v___x_604_);
lean_dec(v_snd_600_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_586_);
v___x_616_ = v___x_597_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_586_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_del_object(v___x_597_);
v___x_618_ = lean_array_fget(v___x_604_, v___x_520_);
v___x_619_ = lean_array_fget(v___x_604_, v___x_525_);
v___x_620_ = lean_array_fget(v___x_604_, v___x_529_);
lean_dec_ref(v___x_604_);
v___x_621_ = l_Lean_Expr_getAppFn(v_target_504_);
lean_dec_ref(v_target_504_);
lean_inc_n(v___x_618_, 2);
v___x_622_ = l_Lean_mkApp3(v___x_621_, v___x_618_, v___x_619_, v___x_620_);
v___x_623_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_618_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_snd_624_; lean_object* v_snd_625_; lean_object* v_a_626_; lean_object* v_fst_627_; lean_object* v_fst_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_663_; 
v_snd_624_ = lean_ctor_get(v_snd_600_, 1);
v_snd_625_ = lean_ctor_get(v_snd_624_, 1);
lean_inc(v_snd_625_);
v_a_626_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_623_, 1);
v_fst_627_ = lean_ctor_get(v_snd_600_, 0);
lean_inc(v_fst_627_);
lean_dec(v_snd_600_);
v_fst_628_ = lean_ctor_get(v_snd_625_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_snd_625_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_snd_625_, 1);
lean_dec(v_unused_664_);
v___x_630_ = v_snd_625_;
v_isShared_631_ = v_isSharedCheck_663_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_fst_628_);
lean_dec(v_snd_625_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_663_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__5));
v___x_633_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6, &l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__6);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_633_);
v___x_635_ = v___x_559_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_tail_557_);
v___x_635_ = v_reuseFailAlloc_662_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 1);
lean_ctor_set(v___x_630_, 1, v___x_635_);
lean_ctor_set(v___x_630_, 0, v_a_626_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_626_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_661_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = l_Lean_mkConst(v___x_632_, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7, &l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___closed__7);
v___x_640_ = l_Lean_mkAppN(v_head_505_, v_args_506_);
lean_inc_ref(v___x_622_);
lean_inc(v_fst_628_);
v___x_641_ = l_Lean_mkApp6(v___x_638_, v___x_618_, v___x_639_, v___x_640_, v_fst_628_, v___x_622_, v_fst_627_);
v___x_642_ = l_Lean_Expr_app___override(v___x_622_, v_fst_628_);
v___x_643_ = l_Lean_MVarId_replaceTargetEq(v_goal_503_, v___x_642_, v___x_641_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_a_644_);
if (v_isShared_647_ == 0)
{
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
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_643_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_643_);
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
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___x_622_);
lean_dec(v___x_618_);
lean_dec(v_snd_600_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec(v_goal_503_);
v_a_665_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_623_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_623_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_673_; lean_object* v___x_675_; 
lean_inc_ref(v_fst_599_);
lean_dec(v_a_595_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v_val_673_ = lean_ctor_get(v_fst_599_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_fst_599_, 1);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_val_673_);
v___x_675_ = v___x_597_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_val_673_);
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
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v_a_678_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_594_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_594_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_acc_571_);
lean_dec_ref(v_curHead_568_);
lean_dec(v_curCL_565_);
lean_del_object(v___x_559_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
v_a_687_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_572_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_572_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_del_object(v___x_559_);
lean_dec(v_tail_557_);
lean_dec_ref_known(v___x_555_, 2);
lean_dec_ref(v_clArgs_550_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_517_;
}
}
}
else
{
lean_dec_ref_known(v___x_555_, 2);
lean_dec(v_tail_556_);
lean_dec_ref(v_clArgs_550_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_517_;
}
}
else
{
lean_dec(v___x_555_);
lean_dec_ref(v_clArgs_550_);
lean_dec_ref(v_head_505_);
lean_dec_ref(v_target_504_);
lean_dec(v_goal_503_);
goto v___jp_517_;
}
}
}
}
}
}
}
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f___boxed(lean_object* v_goal_697_, lean_object* v_target_698_, lean_object* v_head_699_, lean_object* v_args_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f(v_goal_697_, v_target_698_, v_head_699_, v_args_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec_ref(v_args_700_);
return v_res_708_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* runtime_initialize_Std_WP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* initialize_Std_WP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_EPost(builtin);
}
#ifdef __cplusplus
}
#endif
