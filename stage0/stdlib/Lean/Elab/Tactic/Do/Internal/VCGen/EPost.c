// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.EPost
// Imports: public import Lean.Meta.Sym public import Std.Internal.Do public import Lean.Meta.Tactic.Replace
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_3),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value_aux_4),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 64, 94, 8, 151, 53, 87, 57)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tail"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value_aux_4),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 93, 98, 214, 188, 23, 202, 188)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bot_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 109, 99, 66, 8, 241, 194, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "head_bot"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_3),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 9, 164, 51, 74, 122, 246, 113)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg(lean_object* v_range_16_, lean_object* v_b_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_stop_20_; lean_object* v_step_21_; uint8_t v___x_22_; 
v_stop_20_ = lean_ctor_get(v_range_16_, 1);
v_step_21_ = lean_ctor_get(v_range_16_, 2);
v___x_22_ = lean_nat_dec_lt(v_i_18_, v_stop_20_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
lean_dec(v_i_18_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v_b_17_);
return v___x_23_;
}
else
{
lean_object* v_snd_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_50_; 
v_snd_24_ = lean_ctor_get(v_b_17_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_b_17_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v_b_17_, 0);
lean_dec(v_unused_51_);
v___x_26_ = v_b_17_;
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_snd_24_);
lean_dec(v_b_17_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
lean_inc(v_snd_24_);
v___x_34_ = l_Lean_Expr_cleanupAnnotations(v_snd_24_);
v___x_35_ = l_Lean_Expr_isApp(v___x_34_);
if (v___x_35_ == 0)
{
lean_dec_ref(v___x_34_);
lean_dec(v_i_18_);
goto v___jp_28_;
}
else
{
lean_object* v_arg_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_arg_36_ = lean_ctor_get(v___x_34_, 1);
lean_inc_ref(v_arg_36_);
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_34_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec(v_i_18_);
goto v___jp_28_;
}
else
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_40_ = l_Lean_Expr_isApp(v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v___x_39_);
lean_dec_ref(v_arg_36_);
lean_dec(v_i_18_);
goto v___jp_28_;
}
else
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_39_);
v___x_42_ = l_Lean_Expr_isApp(v___x_41_);
if (v___x_42_ == 0)
{
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_36_);
lean_dec(v_i_18_);
goto v___jp_28_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_41_);
v___x_44_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7));
v___x_45_ = l_Lean_Expr_isConstOf(v___x_43_, v___x_44_);
lean_dec_ref(v___x_43_);
if (v___x_45_ == 0)
{
lean_dec_ref(v_arg_36_);
lean_dec(v_i_18_);
goto v___jp_28_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_del_object(v___x_26_);
lean_dec(v_snd_24_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v_arg_36_);
v___x_48_ = lean_nat_add(v_i_18_, v_step_21_);
lean_dec(v_i_18_);
v_b_17_ = v___x_47_;
v_i_18_ = v___x_48_;
goto _start;
}
}
}
}
}
v___jp_28_:
{
lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_29_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__0));
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_29_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_snd_24_);
v___x_31_ = v_reuseFailAlloc_33_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___boxed(lean_object* v_range_52_, lean_object* v_b_53_, lean_object* v_i_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg(v_range_52_, v_b_53_, v_i_54_);
lean_dec_ref(v_range_52_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex(lean_object* v_target_57_, lean_object* v_index_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_101_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v_index_58_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_target_57_);
v___x_74_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg(v___x_71_, v___x_73_, v___x_69_);
lean_dec_ref_known(v___x_71_, 3);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_101_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_101_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_101_;
goto v_resetjp_76_;
}
v___jp_66_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
v_resetjp_76_:
{
lean_object* v_fst_79_; 
v_fst_79_ = lean_ctor_get(v_a_75_, 0);
if (lean_obj_tag(v_fst_79_) == 0)
{
lean_object* v_snd_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_snd_80_ = lean_ctor_get(v_a_75_, 1);
lean_inc(v_snd_80_);
lean_dec(v_a_75_);
v___x_81_ = l_Lean_Expr_cleanupAnnotations(v_snd_80_);
v___x_82_ = l_Lean_Expr_isApp(v___x_81_);
if (v___x_82_ == 0)
{
lean_dec_ref(v___x_81_);
lean_del_object(v___x_77_);
goto v___jp_66_;
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = l_Lean_Expr_appFnCleanup___redArg(v___x_81_);
v___x_84_ = l_Lean_Expr_isApp(v___x_83_);
if (v___x_84_ == 0)
{
lean_dec_ref(v___x_83_);
lean_del_object(v___x_77_);
goto v___jp_66_;
}
else
{
lean_object* v_arg_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_arg_85_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_arg_85_);
v___x_86_ = l_Lean_Expr_appFnCleanup___redArg(v___x_83_);
v___x_87_ = l_Lean_Expr_isApp(v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v___x_86_);
lean_dec_ref(v_arg_85_);
lean_del_object(v___x_77_);
goto v___jp_66_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_86_);
v___x_89_ = l_Lean_Expr_isApp(v___x_88_);
if (v___x_89_ == 0)
{
lean_dec_ref(v___x_88_);
lean_dec_ref(v_arg_85_);
lean_del_object(v___x_77_);
goto v___jp_66_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_88_);
v___x_91_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg___closed__7));
v___x_92_ = l_Lean_Expr_isConstOf(v___x_90_, v___x_91_);
lean_dec_ref(v___x_90_);
if (v___x_92_ == 0)
{
lean_dec_ref(v_arg_85_);
lean_del_object(v___x_77_);
goto v___jp_66_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_arg_85_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_93_);
v___x_95_ = v___x_77_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_97_; lean_object* v___x_99_; 
lean_inc_ref(v_fst_79_);
lean_dec(v_a_75_);
v_val_97_ = lean_ctor_get(v_fst_79_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v_fst_79_, 1);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_val_97_);
v___x_99_ = v___x_77_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_val_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex___boxed(lean_object* v_target_102_, lean_object* v_index_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex(v_target_102_, v_index_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0(lean_object* v_range_112_, lean_object* v_b_113_, lean_object* v_i_114_, lean_object* v_hs_115_, lean_object* v_hl_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___redArg(v_range_112_, v_b_113_, v_i_114_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0___boxed(lean_object* v_range_125_, lean_object* v_b_126_, lean_object* v_i_127_, lean_object* v_hs_128_, lean_object* v_hl_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex_spec__0(v_range_125_, v_b_126_, v_i_127_, v_hs_128_, v_hl_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec_ref(v_range_125_);
return v_res_137_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0(void){
_start:
{
lean_object* v___x_138_; lean_object* v_dummy_139_; 
v___x_138_ = lean_box(0);
v_dummy_139_ = l_Lean_Expr_sort___override(v___x_138_);
return v_dummy_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0(lean_object* v_curr_148_, lean_object* v_idx_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
uint8_t v___y_154_; 
if (lean_obj_tag(v_x_150_) == 5)
{
lean_object* v_fn_163_; lean_object* v_arg_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_fn_163_ = lean_ctor_get(v_x_150_, 0);
lean_inc_ref(v_fn_163_);
v_arg_164_ = lean_ctor_get(v_x_150_, 1);
lean_inc_ref(v_arg_164_);
lean_dec_ref_known(v_x_150_, 2);
v___x_165_ = lean_array_set(v_x_151_, v_x_152_, v_arg_164_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_sub(v_x_152_, v___x_166_);
lean_dec(v_x_152_);
v_x_150_ = v_fn_163_;
v_x_151_ = v___x_165_;
v_x_152_ = v___x_167_;
goto _start;
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
lean_dec(v_x_152_);
v___x_169_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0___closed__1));
v___x_170_ = l_Lean_Expr_isConstOf(v_x_150_, v___x_169_);
lean_dec_ref(v_x_150_);
if (v___x_170_ == 0)
{
v___y_154_ = v___x_170_;
goto v___jp_153_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_array_get_size(v_x_151_);
v___x_173_ = lean_nat_dec_lt(v___x_171_, v___x_172_);
v___y_154_ = v___x_173_;
goto v___jp_153_;
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v_x_151_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_curr_148_);
lean_ctor_set(v___x_155_, 1, v_idx_149_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec_ref(v_curr_148_);
v___x_156_ = l_Lean_instInhabitedExpr;
v___x_157_ = lean_array_get_size(v_x_151_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = lean_nat_sub(v___x_157_, v___x_158_);
v___x_160_ = lean_array_get(v___x_156_, v_x_151_, v___x_159_);
lean_dec(v___x_159_);
lean_dec_ref(v_x_151_);
v___x_161_ = lean_nat_add(v_idx_149_, v___x_158_);
lean_dec(v_idx_149_);
v___x_162_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain(v___x_160_, v___x_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain(lean_object* v_curr_174_, lean_object* v_idx_175_){
_start:
{
lean_object* v___x_176_; lean_object* v_dummy_177_; lean_object* v_nargs_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_176_ = l_Lean_Expr_consumeMData(v_curr_174_);
v_dummy_177_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0);
v_nargs_178_ = l_Lean_Expr_getAppNumArgs(v___x_176_);
lean_inc(v_nargs_178_);
v___x_179_ = lean_mk_array(v_nargs_178_, v_dummy_177_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_sub(v_nargs_178_, v___x_180_);
lean_dec(v_nargs_178_);
v___x_182_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain_spec__0(v_curr_174_, v_idx_175_, v___x_176_, v___x_179_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object* v_tail_210_, lean_object* v_as_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_b_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_lt(v_i_213_, v_sz_212_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v_tail_210_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_b_214_);
return v___x_223_;
}
else
{
lean_object* v_snd_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_470_; 
v_snd_224_ = lean_ctor_get(v_b_214_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_b_214_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_b_214_, 0);
lean_dec(v_unused_471_);
v___x_226_ = v_b_214_;
v_isShared_227_ = v_isSharedCheck_470_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_snd_224_);
lean_dec(v_b_214_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_470_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_snd_228_; lean_object* v_snd_229_; lean_object* v_snd_230_; lean_object* v_fst_231_; 
v_snd_228_ = lean_ctor_get(v_snd_224_, 1);
lean_inc(v_snd_228_);
v_snd_229_ = lean_ctor_get(v_snd_228_, 1);
lean_inc(v_snd_229_);
v_snd_230_ = lean_ctor_get(v_snd_229_, 1);
lean_inc(v_snd_230_);
v_fst_231_ = lean_ctor_get(v_snd_230_, 0);
lean_inc(v_fst_231_);
if (lean_obj_tag(v_fst_231_) == 7)
{
lean_object* v_fst_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_427_; 
v_fst_232_ = lean_ctor_get(v_snd_224_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_snd_224_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v_snd_224_, 1);
lean_dec(v_unused_428_);
v___x_234_ = v_snd_224_;
v_isShared_235_ = v_isSharedCheck_427_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_fst_232_);
lean_dec(v_snd_224_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_427_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_fst_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_425_; 
v_fst_236_ = lean_ctor_get(v_snd_228_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_snd_228_, 1);
lean_dec(v_unused_426_);
v___x_238_ = v_snd_228_;
v_isShared_239_ = v_isSharedCheck_425_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_fst_236_);
lean_dec(v_snd_228_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_425_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_fst_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_423_; 
v_fst_240_ = lean_ctor_get(v_snd_229_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_snd_229_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_snd_229_, 1);
lean_dec(v_unused_424_);
v___x_242_ = v_snd_229_;
v_isShared_243_ = v_isSharedCheck_423_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_fst_240_);
lean_dec(v_snd_229_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_423_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_421_; 
v_snd_244_ = lean_ctor_get(v_snd_230_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_snd_230_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_snd_230_, 0);
lean_dec(v_unused_422_);
v___x_246_ = v_snd_230_;
v_isShared_247_ = v_isSharedCheck_421_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_dec(v_snd_230_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_421_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_binderType_248_; lean_object* v_body_249_; uint8_t v___x_250_; 
v_binderType_248_ = lean_ctor_get(v_fst_231_, 1);
v_body_249_ = lean_ctor_get(v_fst_231_, 2);
v___x_250_ = l_Lean_Expr_hasLooseBVars(v_body_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__3));
v___x_252_ = l_Lean_Expr_isAppOf(v_snd_244_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_tail_210_);
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_247_ == 0)
{
v___x_255_ = v___x_246_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_244_);
v___x_255_ = v_reuseFailAlloc_269_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_255_);
v___x_257_ = v___x_242_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_255_);
v___x_257_ = v_reuseFailAlloc_268_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_257_);
v___x_259_ = v___x_238_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_267_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_259_);
v___x_261_ = v___x_234_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_266_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_261_);
lean_ctor_set(v___x_226_, 0, v___x_253_);
v___x_263_ = v___x_226_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
}
}
else
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Expr_appArg_x21(v_snd_244_);
if (lean_obj_tag(v___x_270_) == 6)
{
lean_object* v_body_271_; lean_object* v___x_272_; 
v_body_271_ = lean_ctor_get(v___x_270_, 2);
lean_inc_ref(v_body_271_);
lean_dec_ref_known(v___x_270_, 3);
lean_inc_ref(v_binderType_248_);
v___x_272_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_248_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
lean_inc_ref(v_body_249_);
v___x_274_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_249_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
lean_inc(v_a_273_);
v___x_276_ = l_Lean_Meta_decLevel(v_a_273_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
lean_inc(v_a_275_);
v___x_278_ = l_Lean_Meta_decLevel(v_a_275_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v_a_280_ = lean_array_uget_borrowed(v_as_211_, v_i_213_);
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__6));
lean_inc(v_tail_210_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v_a_279_);
lean_ctor_set(v___x_282_, 1, v_tail_210_);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v_a_277_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l_Lean_mkConst(v___x_281_, v___x_283_);
lean_inc(v_a_280_);
lean_inc_ref(v_body_271_);
lean_inc_ref(v_body_249_);
lean_inc_ref(v_binderType_248_);
v___x_285_ = l_Lean_mkApp4(v___x_284_, v_binderType_248_, v_body_249_, v_body_271_, v_a_280_);
lean_inc_ref(v___x_285_);
v___x_286_ = l_Lean_Meta_Sym_inferType(v___x_285_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_346_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_346_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_346_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_346_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8));
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = l_Lean_Expr_isAppOfArity(v_a_287_, v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_a_287_);
lean_dec_ref(v___x_285_);
lean_dec(v_a_275_);
lean_dec(v_a_273_);
lean_dec_ref(v_body_271_);
lean_dec(v_tail_210_);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_247_ == 0)
{
v___x_296_ = v___x_246_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_snd_244_);
v___x_296_ = v_reuseFailAlloc_312_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_296_);
v___x_298_ = v___x_242_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_311_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_298_);
v___x_300_ = v___x_238_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_310_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_300_);
v___x_302_ = v___x_234_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_309_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_302_);
lean_ctor_set(v___x_226_, 0, v___x_294_);
v___x_304_ = v___x_226_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_302_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_304_);
v___x_306_ = v___x_289_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_inc_ref_n(v_body_249_, 3);
lean_inc_ref_n(v_binderType_248_, 2);
lean_del_object(v___x_289_);
lean_dec(v_snd_244_);
lean_dec_ref_known(v_fst_231_, 3);
v___x_313_ = lean_box(0);
v___x_314_ = l_Lean_Expr_appArg_x21(v_a_287_);
lean_dec(v_a_287_);
v___x_315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__10));
lean_inc(v_tail_210_);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_275_);
lean_ctor_set(v___x_316_, 1, v_tail_210_);
lean_inc_ref(v___x_316_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v_a_273_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_mkConst(v___x_315_, v___x_317_);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__12));
v___x_320_ = 0;
v___x_321_ = l_Lean_Expr_lam___override(v___x_319_, v_binderType_248_, v_body_249_, v___x_320_);
lean_inc_n(v_a_280_, 3);
lean_inc(v_fst_240_);
lean_inc(v_fst_236_);
v___x_322_ = l_Lean_mkApp6(v___x_318_, v_binderType_248_, v___x_321_, v_fst_236_, v_fst_240_, v_fst_232_, v_a_280_);
v___x_323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__14));
v___x_324_ = l_Lean_mkConst(v___x_323_, v___x_316_);
v___x_325_ = l_Lean_Expr_app___override(v_fst_236_, v_a_280_);
v___x_326_ = l_Lean_Expr_app___override(v_fst_240_, v_a_280_);
lean_inc_ref(v___x_314_);
lean_inc_ref(v___x_325_);
v___x_327_ = l_Lean_mkApp6(v___x_324_, v_body_249_, v___x_325_, v___x_326_, v___x_314_, v___x_322_, v___x_285_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_body_271_);
lean_ctor_set(v___x_246_, 0, v_body_249_);
v___x_329_ = v___x_246_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_body_249_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_body_271_);
v___x_329_ = v_reuseFailAlloc_345_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_329_);
lean_ctor_set(v___x_242_, 0, v___x_314_);
v___x_331_ = v___x_242_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_344_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_331_);
lean_ctor_set(v___x_238_, 0, v___x_325_);
v___x_333_ = v___x_238_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_343_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_333_);
lean_ctor_set(v___x_234_, 0, v___x_327_);
v___x_335_ = v___x_234_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_342_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_335_);
lean_ctor_set(v___x_226_, 0, v___x_313_);
v___x_337_ = v___x_226_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
size_t v___x_338_; size_t v___x_339_; 
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_add(v_i_213_, v___x_338_);
v_i_213_ = v___x_339_;
v_b_214_ = v___x_337_;
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
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___x_285_);
lean_dec(v_a_275_);
lean_dec(v_a_273_);
lean_dec_ref(v_body_271_);
lean_del_object(v___x_246_);
lean_dec(v_snd_244_);
lean_del_object(v___x_242_);
lean_dec(v_fst_240_);
lean_del_object(v___x_238_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec_ref_known(v_fst_231_, 3);
lean_dec(v_fst_232_);
lean_del_object(v___x_226_);
lean_dec(v_tail_210_);
v_a_347_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_286_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_286_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_a_277_);
lean_dec(v_a_275_);
lean_dec(v_a_273_);
lean_dec_ref(v_body_271_);
lean_del_object(v___x_246_);
lean_dec(v_snd_244_);
lean_del_object(v___x_242_);
lean_dec(v_fst_240_);
lean_del_object(v___x_238_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec_ref_known(v_fst_231_, 3);
lean_dec(v_fst_232_);
lean_del_object(v___x_226_);
lean_dec(v_tail_210_);
v_a_355_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_278_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_278_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_a_275_);
lean_dec(v_a_273_);
lean_dec_ref(v_body_271_);
lean_del_object(v___x_246_);
lean_dec(v_snd_244_);
lean_del_object(v___x_242_);
lean_dec(v_fst_240_);
lean_del_object(v___x_238_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec_ref_known(v_fst_231_, 3);
lean_dec(v_fst_232_);
lean_del_object(v___x_226_);
lean_dec(v_tail_210_);
v_a_363_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_276_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_276_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_273_);
lean_dec_ref(v_body_271_);
lean_del_object(v___x_246_);
lean_dec(v_snd_244_);
lean_del_object(v___x_242_);
lean_dec(v_fst_240_);
lean_del_object(v___x_238_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec_ref_known(v_fst_231_, 3);
lean_dec(v_fst_232_);
lean_del_object(v___x_226_);
lean_dec(v_tail_210_);
v_a_371_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_274_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_274_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref(v_body_271_);
lean_del_object(v___x_246_);
lean_dec(v_snd_244_);
lean_del_object(v___x_242_);
lean_dec(v_fst_240_);
lean_del_object(v___x_238_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec_ref_known(v_fst_231_, 3);
lean_dec(v_fst_232_);
lean_del_object(v___x_226_);
lean_dec(v_tail_210_);
v_a_379_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_272_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_272_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
lean_dec_ref(v___x_270_);
lean_dec(v_tail_210_);
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_247_ == 0)
{
v___x_389_ = v___x_246_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_snd_244_);
v___x_389_ = v_reuseFailAlloc_403_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_389_);
v___x_391_ = v___x_242_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_402_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_391_);
v___x_393_ = v___x_238_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_401_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_393_);
v___x_395_ = v___x_234_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_400_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_395_);
lean_ctor_set(v___x_226_, 0, v___x_387_);
v___x_397_ = v___x_226_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
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
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_dec(v_tail_210_);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_247_ == 0)
{
v___x_406_ = v___x_246_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_snd_244_);
v___x_406_ = v_reuseFailAlloc_420_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_406_);
v___x_408_ = v___x_242_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_419_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_408_);
v___x_410_ = v___x_238_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_418_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_410_);
v___x_412_ = v___x_234_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_417_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_412_);
lean_ctor_set(v___x_226_, 0, v___x_404_);
v___x_414_ = v___x_226_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
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
lean_object* v_fst_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_tail_210_);
v_fst_429_ = lean_ctor_get(v_snd_224_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_snd_224_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v_snd_224_, 1);
lean_dec(v_unused_469_);
v___x_431_ = v_snd_224_;
v_isShared_432_ = v_isSharedCheck_468_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_fst_429_);
lean_dec(v_snd_224_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_468_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_466_; 
v_fst_433_ = lean_ctor_get(v_snd_228_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_snd_228_, 1);
lean_dec(v_unused_467_);
v___x_435_ = v_snd_228_;
v_isShared_436_ = v_isSharedCheck_466_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_fst_433_);
lean_dec(v_snd_228_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_466_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_fst_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_464_; 
v_fst_437_ = lean_ctor_get(v_snd_229_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_snd_229_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_snd_229_, 1);
lean_dec(v_unused_465_);
v___x_439_ = v_snd_229_;
v_isShared_440_ = v_isSharedCheck_464_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_fst_437_);
lean_dec(v_snd_229_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_464_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_462_; 
v_snd_441_ = lean_ctor_get(v_snd_230_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_snd_230_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v_snd_230_, 0);
lean_dec(v_unused_463_);
v___x_443_ = v_snd_230_;
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_dec(v_snd_230_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__4));
if (v_isShared_444_ == 0)
{
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_snd_441_);
v___x_447_ = v_reuseFailAlloc_461_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_447_);
v___x_449_ = v___x_439_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_460_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_449_);
v___x_451_ = v___x_435_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_459_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_451_);
v___x_453_ = v___x_431_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_458_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_453_);
lean_ctor_set(v___x_226_, 0, v___x_445_);
v___x_455_ = v___x_226_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object* v_tail_472_, lean_object* v_as_473_, lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
size_t v_sz_boxed_484_; size_t v_i_boxed_485_; lean_object* v_res_486_; 
v_sz_boxed_484_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_485_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(v_tail_472_, v_as_473_, v_sz_boxed_484_, v_i_boxed_485_, v_b_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v_as_473_);
return v_res_486_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = l_Lean_Level_succ___override(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_box(0);
v___x_506_ = l_Lean_mkSort(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(lean_object* v_goal_507_, lean_object* v_target_508_, lean_object* v_head_509_, lean_object* v_args_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_args_510_);
v___x_526_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_dec_lt(v___x_529_, v___x_525_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = lean_nat_dec_lt(v___x_533_, v___x_525_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_array_fget_borrowed(v_args_510_, v___x_533_);
lean_inc(v___x_537_);
v___x_538_ = l_Lean_Expr_cleanupAnnotations(v___x_537_);
v___x_539_ = l_Lean_Expr_isApp(v___x_538_);
if (v___x_539_ == 0)
{
lean_dec_ref(v___x_538_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_518_;
}
else
{
lean_object* v_arg_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_arg_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc_ref(v_arg_540_);
v___x_541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_538_);
v___x_542_ = l_Lean_Expr_isApp(v___x_541_);
if (v___x_542_ == 0)
{
lean_dec_ref(v___x_541_);
lean_dec_ref(v_arg_540_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_518_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_541_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1));
v___x_545_ = l_Lean_Expr_isConstOf(v___x_543_, v___x_544_);
lean_dec_ref(v___x_543_);
if (v___x_545_ == 0)
{
lean_dec_ref(v_arg_540_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_518_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_Expr_isApp(v_arg_540_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_arg_540_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v_dummy_550_; lean_object* v_nargs_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_clArgs_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_549_ = l_Lean_Expr_appArg_x21(v_arg_540_);
lean_dec_ref(v_arg_540_);
v_dummy_550_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0);
v_nargs_551_ = l_Lean_Expr_getAppNumArgs(v___x_549_);
lean_inc(v_nargs_551_);
v___x_552_ = lean_mk_array(v_nargs_551_, v_dummy_550_);
v___x_553_ = lean_nat_sub(v_nargs_551_, v___x_529_);
lean_dec(v_nargs_551_);
v_clArgs_554_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_549_, v___x_552_, v___x_553_);
v___x_555_ = lean_array_get_size(v_clArgs_554_);
v___x_556_ = lean_nat_dec_le(v___x_533_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v_clArgs_554_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Expr_constLevels_x21(v_head_509_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_tail_560_; 
v_tail_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_tail_560_);
if (lean_obj_tag(v_tail_560_) == 1)
{
lean_object* v_tail_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_699_; 
v_tail_561_ = lean_ctor_get(v_tail_560_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_tail_560_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_tail_560_, 0);
lean_dec(v_unused_700_);
v___x_563_ = v_tail_560_;
v_isShared_564_ = v_isSharedCheck_699_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_tail_561_);
lean_dec(v_tail_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_699_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
if (lean_obj_tag(v_tail_561_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_curCL_569_; lean_object* v___x_570_; lean_object* v_ctInst_571_; lean_object* v_curHead_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_acc_575_; lean_object* v___x_576_; 
v___x_565_ = l_Lean_instInhabitedExpr;
v___x_566_ = lean_array_fget_borrowed(v_args_510_, v___x_524_);
v___x_567_ = lean_array_fget_borrowed(v_args_510_, v___x_529_);
v___x_568_ = lean_nat_sub(v___x_555_, v___x_533_);
v_curCL_569_ = lean_array_get(v___x_565_, v_clArgs_554_, v___x_568_);
lean_dec(v___x_568_);
v___x_570_ = lean_nat_sub(v___x_555_, v___x_529_);
v_ctInst_571_ = lean_array_get(v___x_565_, v_clArgs_554_, v___x_570_);
lean_dec(v___x_570_);
lean_dec_ref(v_clArgs_554_);
lean_inc(v___x_537_);
lean_inc_n(v___x_567_, 2);
lean_inc_n(v___x_566_, 2);
lean_inc_ref(v_head_509_);
v_curHead_572_ = l_Lean_mkApp3(v_head_509_, v___x_566_, v___x_567_, v___x_537_);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3));
v___x_574_ = l_Lean_mkConst(v___x_573_, v___x_559_);
lean_inc(v_curCL_569_);
v_acc_575_ = l_Lean_mkApp4(v___x_574_, v___x_566_, v___x_567_, v_curCL_569_, v_ctInst_571_);
lean_inc_ref(v_acc_575_);
v___x_576_ = l_Lean_Meta_Sym_inferType(v_acc_575_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_690_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_690_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_690_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_690_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___closed__8));
v___x_582_ = lean_unsigned_to_nat(3u);
v___x_583_ = l_Lean_Expr_isAppOfArity(v_a_577_, v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_586_; 
lean_dec(v_a_577_);
lean_dec_ref(v_acc_575_);
lean_dec_ref(v_curHead_572_);
lean_dec(v_curCL_569_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v___x_584_ = lean_box(0);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
lean_del_object(v___x_579_);
v___x_588_ = l_Lean_Expr_appArg_x21(v_a_577_);
lean_dec(v_a_577_);
v___x_589_ = l_Array_extract___redArg(v_args_510_, v___x_582_, v___x_525_);
v___x_590_ = lean_box(0);
lean_inc(v___x_566_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_566_);
lean_ctor_set(v___x_591_, 1, v_curCL_569_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_588_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_curHead_572_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_acc_575_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_590_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v_sz_596_ = lean_array_size(v___x_589_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(v_tail_561_, v___x_589_, v_sz_596_, v___x_597_, v___x_595_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec_ref(v___x_589_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_681_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_681_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_681_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_681_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
if (lean_obj_tag(v_fst_603_) == 0)
{
lean_object* v_snd_604_; lean_object* v_nargs_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_snd_604_ = lean_ctor_get(v_a_599_, 1);
lean_inc(v_snd_604_);
lean_dec(v_a_599_);
v_nargs_605_ = l_Lean_Expr_getAppNumArgs(v_target_508_);
lean_inc(v_nargs_605_);
v___x_606_ = lean_mk_array(v_nargs_605_, v_dummy_550_);
v___x_607_ = lean_nat_sub(v_nargs_605_, v___x_529_);
lean_dec(v_nargs_605_);
lean_inc_ref(v_target_508_);
v___x_608_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_508_, v___x_606_, v___x_607_);
v___x_609_ = lean_array_get_size(v___x_608_);
v___x_610_ = lean_nat_dec_lt(v___x_524_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v___x_608_);
lean_dec(v_snd_604_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_590_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_590_);
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
v___x_614_ = lean_nat_dec_lt(v___x_529_, v___x_609_);
if (v___x_614_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v___x_608_);
lean_dec(v_snd_604_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_590_);
v___x_616_ = v___x_601_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_590_);
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
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v___x_533_, v___x_609_);
if (v___x_618_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v___x_608_);
lean_dec(v_snd_604_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_590_);
v___x_620_ = v___x_601_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_590_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_del_object(v___x_601_);
v___x_622_ = lean_array_fget(v___x_608_, v___x_524_);
v___x_623_ = lean_array_fget(v___x_608_, v___x_529_);
v___x_624_ = lean_array_fget(v___x_608_, v___x_533_);
lean_dec_ref(v___x_608_);
v___x_625_ = l_Lean_Expr_getAppFn(v_target_508_);
lean_dec_ref(v_target_508_);
lean_inc_n(v___x_622_, 2);
v___x_626_ = l_Lean_mkApp3(v___x_625_, v___x_622_, v___x_623_, v___x_624_);
v___x_627_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_622_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_snd_628_; lean_object* v_snd_629_; lean_object* v_a_630_; lean_object* v_fst_631_; lean_object* v_fst_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_667_; 
v_snd_628_ = lean_ctor_get(v_snd_604_, 1);
v_snd_629_ = lean_ctor_get(v_snd_628_, 1);
lean_inc(v_snd_629_);
v_a_630_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_627_, 1);
v_fst_631_ = lean_ctor_get(v_snd_604_, 0);
lean_inc(v_fst_631_);
lean_dec(v_snd_604_);
v_fst_632_ = lean_ctor_get(v_snd_629_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_snd_629_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_snd_629_, 1);
lean_dec(v_unused_668_);
v___x_634_ = v_snd_629_;
v_isShared_635_ = v_isSharedCheck_667_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_fst_632_);
lean_dec(v_snd_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_667_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__5));
v___x_637_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_637_);
v___x_639_ = v___x_563_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_tail_561_);
v___x_639_ = v_reuseFailAlloc_666_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 1);
lean_ctor_set(v___x_634_, 1, v___x_639_);
lean_ctor_set(v___x_634_, 0, v_a_630_);
v___x_641_ = v___x_634_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_630_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_639_);
v___x_641_ = v_reuseFailAlloc_665_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_642_ = l_Lean_mkConst(v___x_636_, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7);
v___x_644_ = l_Lean_mkAppN(v_head_509_, v_args_510_);
lean_inc_ref(v___x_626_);
lean_inc(v_fst_632_);
v___x_645_ = l_Lean_mkApp6(v___x_642_, v___x_622_, v___x_643_, v___x_644_, v_fst_632_, v___x_626_, v_fst_631_);
v___x_646_ = l_Lean_Expr_app___override(v___x_626_, v_fst_632_);
v___x_647_ = l_Lean_MVarId_replaceTargetEq(v_goal_507_, v___x_646_, v___x_645_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_a_648_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_a_657_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_647_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v___x_626_);
lean_dec(v___x_622_);
lean_dec(v_snd_604_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec(v_goal_507_);
v_a_669_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_627_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_627_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
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
}
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; 
lean_inc_ref(v_fst_603_);
lean_dec(v_a_599_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v_val_677_ = lean_ctor_get(v_fst_603_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_fst_603_, 1);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_val_677_);
v___x_679_ = v___x_601_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v_a_682_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_598_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_598_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_acc_575_);
lean_dec_ref(v_curHead_572_);
lean_dec(v_curCL_569_);
lean_del_object(v___x_563_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
v_a_691_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_576_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_576_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
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
else
{
lean_del_object(v___x_563_);
lean_dec(v_tail_561_);
lean_dec_ref_known(v___x_559_, 2);
lean_dec_ref(v_clArgs_554_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_521_;
}
}
}
else
{
lean_dec_ref_known(v___x_559_, 2);
lean_dec(v_tail_560_);
lean_dec_ref(v_clArgs_554_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_521_;
}
}
else
{
lean_dec(v___x_559_);
lean_dec_ref(v_clArgs_554_);
lean_dec_ref(v_head_509_);
lean_dec_ref(v_target_508_);
lean_dec(v_goal_507_);
goto v___jp_521_;
}
}
}
}
}
}
}
}
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___boxed(lean_object* v_goal_701_, lean_object* v_target_702_, lean_object* v_head_703_, lean_object* v_args_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(v_goal_701_, v_target_702_, v_head_703_, v_args_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_args_704_);
return v_res_712_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* initialize_Std_Internal_Do(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(builtin);
}
#ifdef __cplusplus
}
#endif
