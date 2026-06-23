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
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bot_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 109, 99, 66, 8, 241, 194, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg(lean_object* v_tail_210_, lean_object* v_as_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_b_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_lt(v_i_213_, v_sz_212_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v_tail_210_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v_b_214_);
return v___x_222_;
}
else
{
lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_469_; 
v_snd_223_ = lean_ctor_get(v_b_214_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_b_214_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_b_214_, 0);
lean_dec(v_unused_470_);
v___x_225_ = v_b_214_;
v_isShared_226_ = v_isSharedCheck_469_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_dec(v_b_214_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_469_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_snd_227_; lean_object* v_snd_228_; lean_object* v_snd_229_; lean_object* v_fst_230_; 
v_snd_227_ = lean_ctor_get(v_snd_223_, 1);
lean_inc(v_snd_227_);
v_snd_228_ = lean_ctor_get(v_snd_227_, 1);
lean_inc(v_snd_228_);
v_snd_229_ = lean_ctor_get(v_snd_228_, 1);
lean_inc(v_snd_229_);
v_fst_230_ = lean_ctor_get(v_snd_229_, 0);
lean_inc(v_fst_230_);
if (lean_obj_tag(v_fst_230_) == 7)
{
lean_object* v_fst_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_426_; 
v_fst_231_ = lean_ctor_get(v_snd_223_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_snd_223_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_snd_223_, 1);
lean_dec(v_unused_427_);
v___x_233_ = v_snd_223_;
v_isShared_234_ = v_isSharedCheck_426_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_fst_231_);
lean_dec(v_snd_223_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_426_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_fst_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_424_; 
v_fst_235_ = lean_ctor_get(v_snd_227_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_snd_227_, 1);
lean_dec(v_unused_425_);
v___x_237_ = v_snd_227_;
v_isShared_238_ = v_isSharedCheck_424_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_fst_235_);
lean_dec(v_snd_227_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_424_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_fst_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_422_; 
v_fst_239_ = lean_ctor_get(v_snd_228_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_snd_228_, 1);
lean_dec(v_unused_423_);
v___x_241_ = v_snd_228_;
v_isShared_242_ = v_isSharedCheck_422_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_fst_239_);
lean_dec(v_snd_228_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_422_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_420_; 
v_snd_243_ = lean_ctor_get(v_snd_229_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_snd_229_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_snd_229_, 0);
lean_dec(v_unused_421_);
v___x_245_ = v_snd_229_;
v_isShared_246_ = v_isSharedCheck_420_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_dec(v_snd_229_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_420_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_binderType_247_; lean_object* v_body_248_; uint8_t v___x_249_; 
v_binderType_247_ = lean_ctor_get(v_fst_230_, 1);
v_body_248_ = lean_ctor_get(v_fst_230_, 2);
v___x_249_ = l_Lean_Expr_hasLooseBVars(v_body_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__3));
v___x_251_ = l_Lean_Expr_isAppOf(v_snd_243_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec(v_tail_210_);
v___x_252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4));
if (v_isShared_246_ == 0)
{
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_snd_243_);
v___x_254_ = v_reuseFailAlloc_268_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_254_);
v___x_256_ = v___x_241_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_267_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_256_);
v___x_258_ = v___x_237_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_235_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_266_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_258_);
v___x_260_ = v___x_233_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_260_);
lean_ctor_set(v___x_225_, 0, v___x_252_);
v___x_262_ = v___x_225_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_264_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
}
}
}
else
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Expr_appArg_x21(v_snd_243_);
if (lean_obj_tag(v___x_269_) == 6)
{
lean_object* v_body_270_; lean_object* v___x_271_; 
v_body_270_ = lean_ctor_get(v___x_269_, 2);
lean_inc_ref(v_body_270_);
lean_dec_ref_known(v___x_269_, 3);
lean_inc_ref(v_binderType_247_);
v___x_271_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_247_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
lean_inc_ref(v_body_248_);
v___x_273_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_248_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
lean_inc(v_a_272_);
v___x_275_ = l_Lean_Meta_decLevel(v_a_272_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
lean_inc(v_a_274_);
v___x_277_ = l_Lean_Meta_decLevel(v_a_274_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
v_a_279_ = lean_array_uget_borrowed(v_as_211_, v_i_213_);
v___x_280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__6));
lean_inc(v_tail_210_);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_278_);
lean_ctor_set(v___x_281_, 1, v_tail_210_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v_a_276_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_mkConst(v___x_280_, v___x_282_);
lean_inc(v_a_279_);
lean_inc_ref(v_body_270_);
lean_inc_ref(v_body_248_);
lean_inc_ref(v_binderType_247_);
v___x_284_ = l_Lean_mkApp4(v___x_283_, v_binderType_247_, v_body_248_, v_body_270_, v_a_279_);
lean_inc_ref(v___x_284_);
v___x_285_ = l_Lean_Meta_Sym_inferType___redArg(v___x_284_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_345_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_345_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_345_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_345_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__8));
v___x_291_ = lean_unsigned_to_nat(3u);
v___x_292_ = l_Lean_Expr_isAppOfArity(v_a_286_, v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_a_286_);
lean_dec_ref(v___x_284_);
lean_dec(v_a_274_);
lean_dec(v_a_272_);
lean_dec_ref(v_body_270_);
lean_dec(v_tail_210_);
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4));
if (v_isShared_246_ == 0)
{
v___x_295_ = v___x_245_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_snd_243_);
v___x_295_ = v_reuseFailAlloc_311_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_295_);
v___x_297_ = v___x_241_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_310_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_297_);
v___x_299_ = v___x_237_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_235_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_309_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_299_);
v___x_301_ = v___x_233_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_308_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_301_);
lean_ctor_set(v___x_225_, 0, v___x_293_);
v___x_303_ = v___x_225_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_303_);
v___x_305_ = v___x_288_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_inc_ref_n(v_body_248_, 3);
lean_inc_ref_n(v_binderType_247_, 2);
lean_del_object(v___x_288_);
lean_dec(v_snd_243_);
lean_dec_ref_known(v_fst_230_, 3);
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_Expr_appArg_x21(v_a_286_);
lean_dec(v_a_286_);
v___x_314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__10));
lean_inc(v_tail_210_);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_a_274_);
lean_ctor_set(v___x_315_, 1, v_tail_210_);
lean_inc_ref(v___x_315_);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_272_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_mkConst(v___x_314_, v___x_316_);
v___x_318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__12));
v___x_319_ = 0;
v___x_320_ = l_Lean_Expr_lam___override(v___x_318_, v_binderType_247_, v_body_248_, v___x_319_);
lean_inc_n(v_a_279_, 3);
lean_inc(v_fst_239_);
lean_inc(v_fst_235_);
v___x_321_ = l_Lean_mkApp6(v___x_317_, v_binderType_247_, v___x_320_, v_fst_235_, v_fst_239_, v_fst_231_, v_a_279_);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__14));
v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_315_);
v___x_324_ = l_Lean_Expr_app___override(v_fst_235_, v_a_279_);
v___x_325_ = l_Lean_Expr_app___override(v_fst_239_, v_a_279_);
lean_inc_ref(v___x_313_);
lean_inc_ref(v___x_324_);
v___x_326_ = l_Lean_mkApp6(v___x_323_, v_body_248_, v___x_324_, v___x_325_, v___x_313_, v___x_321_, v___x_284_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_body_270_);
lean_ctor_set(v___x_245_, 0, v_body_248_);
v___x_328_ = v___x_245_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_body_248_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_body_270_);
v___x_328_ = v_reuseFailAlloc_344_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_328_);
lean_ctor_set(v___x_241_, 0, v___x_313_);
v___x_330_ = v___x_241_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_343_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_330_);
lean_ctor_set(v___x_237_, 0, v___x_324_);
v___x_332_ = v___x_237_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_342_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_332_);
lean_ctor_set(v___x_233_, 0, v___x_326_);
v___x_334_ = v___x_233_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_341_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_334_);
lean_ctor_set(v___x_225_, 0, v___x_312_);
v___x_336_ = v___x_225_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
size_t v___x_337_; size_t v___x_338_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_213_, v___x_337_);
v_i_213_ = v___x_338_;
v_b_214_ = v___x_336_;
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
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___x_284_);
lean_dec(v_a_274_);
lean_dec(v_a_272_);
lean_dec_ref(v_body_270_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_del_object(v___x_241_);
lean_dec(v_fst_239_);
lean_del_object(v___x_237_);
lean_dec(v_fst_235_);
lean_del_object(v___x_233_);
lean_dec_ref_known(v_fst_230_, 3);
lean_dec(v_fst_231_);
lean_del_object(v___x_225_);
lean_dec(v_tail_210_);
v_a_346_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_285_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_285_);
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
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_276_);
lean_dec(v_a_274_);
lean_dec(v_a_272_);
lean_dec_ref(v_body_270_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_del_object(v___x_241_);
lean_dec(v_fst_239_);
lean_del_object(v___x_237_);
lean_dec(v_fst_235_);
lean_del_object(v___x_233_);
lean_dec_ref_known(v_fst_230_, 3);
lean_dec(v_fst_231_);
lean_del_object(v___x_225_);
lean_dec(v_tail_210_);
v_a_354_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_277_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_277_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_274_);
lean_dec(v_a_272_);
lean_dec_ref(v_body_270_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_del_object(v___x_241_);
lean_dec(v_fst_239_);
lean_del_object(v___x_237_);
lean_dec(v_fst_235_);
lean_del_object(v___x_233_);
lean_dec_ref_known(v_fst_230_, 3);
lean_dec(v_fst_231_);
lean_del_object(v___x_225_);
lean_dec(v_tail_210_);
v_a_362_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_275_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_275_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_a_272_);
lean_dec_ref(v_body_270_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_del_object(v___x_241_);
lean_dec(v_fst_239_);
lean_del_object(v___x_237_);
lean_dec(v_fst_235_);
lean_del_object(v___x_233_);
lean_dec_ref_known(v_fst_230_, 3);
lean_dec(v_fst_231_);
lean_del_object(v___x_225_);
lean_dec(v_tail_210_);
v_a_370_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_273_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_273_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec_ref(v_body_270_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_del_object(v___x_241_);
lean_dec(v_fst_239_);
lean_del_object(v___x_237_);
lean_dec(v_fst_235_);
lean_del_object(v___x_233_);
lean_dec_ref_known(v_fst_230_, 3);
lean_dec(v_fst_231_);
lean_del_object(v___x_225_);
lean_dec(v_tail_210_);
v_a_378_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_271_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_271_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec_ref(v___x_269_);
lean_dec(v_tail_210_);
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4));
if (v_isShared_246_ == 0)
{
v___x_388_ = v___x_245_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_snd_243_);
v___x_388_ = v_reuseFailAlloc_402_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_388_);
v___x_390_ = v___x_241_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_401_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_390_);
v___x_392_ = v___x_237_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_235_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_400_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_392_);
v___x_394_ = v___x_233_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_399_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_394_);
lean_ctor_set(v___x_225_, 0, v___x_386_);
v___x_396_ = v___x_225_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_398_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
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
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_dec(v_tail_210_);
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4));
if (v_isShared_246_ == 0)
{
v___x_405_ = v___x_245_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_243_);
v___x_405_ = v_reuseFailAlloc_419_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_405_);
v___x_407_ = v___x_241_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_418_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_407_);
v___x_409_ = v___x_237_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_235_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_417_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_409_);
v___x_411_ = v___x_233_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_416_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_411_);
lean_ctor_set(v___x_225_, 0, v___x_403_);
v___x_413_ = v___x_225_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
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
lean_object* v_fst_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_tail_210_);
v_fst_428_ = lean_ctor_get(v_snd_223_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_snd_223_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v_snd_223_, 1);
lean_dec(v_unused_468_);
v___x_430_ = v_snd_223_;
v_isShared_431_ = v_isSharedCheck_467_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_fst_428_);
lean_dec(v_snd_223_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_467_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_465_; 
v_fst_432_ = lean_ctor_get(v_snd_227_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_snd_227_, 1);
lean_dec(v_unused_466_);
v___x_434_ = v_snd_227_;
v_isShared_435_ = v_isSharedCheck_465_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_snd_227_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_465_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_463_; 
v_fst_436_ = lean_ctor_get(v_snd_228_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_snd_228_, 1);
lean_dec(v_unused_464_);
v___x_438_ = v_snd_228_;
v_isShared_439_ = v_isSharedCheck_463_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_fst_436_);
lean_dec(v_snd_228_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_463_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_461_; 
v_snd_440_ = lean_ctor_get(v_snd_229_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_snd_229_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_snd_229_, 0);
lean_dec(v_unused_462_);
v___x_442_ = v_snd_229_;
v_isShared_443_ = v_isSharedCheck_461_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_dec(v_snd_229_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_461_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__4));
if (v_isShared_443_ == 0)
{
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_snd_440_);
v___x_446_ = v_reuseFailAlloc_460_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_446_);
v___x_448_ = v___x_438_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_436_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_459_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_448_);
v___x_450_ = v___x_434_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_432_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_458_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_450_);
v___x_452_ = v___x_430_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_457_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_452_);
lean_ctor_set(v___x_225_, 0, v___x_444_);
v___x_454_ = v___x_225_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___boxed(lean_object* v_tail_471_, lean_object* v_as_472_, lean_object* v_sz_473_, lean_object* v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_473_);
lean_dec(v_sz_473_);
v_i_boxed_483_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg(v_tail_471_, v_as_472_, v_sz_boxed_482_, v_i_boxed_483_, v_b_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v_as_472_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_Level_succ___override(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = l_Lean_mkSort(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(lean_object* v_goal_505_, lean_object* v_target_506_, lean_object* v_head_507_, lean_object* v_args_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_array_get_size(v_args_508_);
v___x_524_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_dec_lt(v___x_527_, v___x_523_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = lean_nat_dec_lt(v___x_531_, v___x_523_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_array_fget_borrowed(v_args_508_, v___x_531_);
lean_inc(v___x_535_);
v___x_536_ = l_Lean_Expr_cleanupAnnotations(v___x_535_);
v___x_537_ = l_Lean_Expr_isApp(v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v___x_536_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_516_;
}
else
{
lean_object* v_arg_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_arg_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc_ref(v_arg_538_);
v___x_539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_536_);
v___x_540_ = l_Lean_Expr_isApp(v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v___x_539_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_516_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_539_);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__1));
v___x_543_ = l_Lean_Expr_isConstOf(v___x_541_, v___x_542_);
lean_dec_ref(v___x_541_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_516_;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = l_Lean_Expr_isApp(v_arg_538_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v_dummy_548_; lean_object* v_nargs_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_clArgs_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_547_ = l_Lean_Expr_appArg_x21(v_arg_538_);
lean_dec_ref(v_arg_538_);
v_dummy_548_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain___closed__0);
v_nargs_549_ = l_Lean_Expr_getAppNumArgs(v___x_547_);
lean_inc(v_nargs_549_);
v___x_550_ = lean_mk_array(v_nargs_549_, v_dummy_548_);
v___x_551_ = lean_nat_sub(v_nargs_549_, v___x_527_);
lean_dec(v_nargs_549_);
v_clArgs_552_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_547_, v___x_550_, v___x_551_);
v___x_553_ = lean_array_get_size(v_clArgs_552_);
v___x_554_ = lean_nat_dec_le(v___x_531_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_clArgs_552_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Expr_constLevels_x21(v_head_507_);
if (lean_obj_tag(v___x_557_) == 1)
{
lean_object* v_tail_558_; 
v_tail_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_tail_558_);
if (lean_obj_tag(v_tail_558_) == 1)
{
lean_object* v_tail_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_697_; 
v_tail_559_ = lean_ctor_get(v_tail_558_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_tail_558_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_tail_558_, 0);
lean_dec(v_unused_698_);
v___x_561_ = v_tail_558_;
v_isShared_562_ = v_isSharedCheck_697_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_tail_559_);
lean_dec(v_tail_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_697_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_tail_559_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_curCL_567_; lean_object* v___x_568_; lean_object* v_ctInst_569_; lean_object* v_curHead_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_acc_573_; lean_object* v___x_574_; 
v___x_563_ = l_Lean_instInhabitedExpr;
v___x_564_ = lean_array_fget_borrowed(v_args_508_, v___x_522_);
v___x_565_ = lean_array_fget_borrowed(v_args_508_, v___x_527_);
v___x_566_ = lean_nat_sub(v___x_553_, v___x_531_);
v_curCL_567_ = lean_array_get(v___x_563_, v_clArgs_552_, v___x_566_);
lean_dec(v___x_566_);
v___x_568_ = lean_nat_sub(v___x_553_, v___x_527_);
v_ctInst_569_ = lean_array_get(v___x_563_, v_clArgs_552_, v___x_568_);
lean_dec(v___x_568_);
lean_dec_ref(v_clArgs_552_);
lean_inc(v___x_535_);
lean_inc_n(v___x_565_, 2);
lean_inc_n(v___x_564_, 2);
lean_inc_ref(v_head_507_);
v_curHead_570_ = l_Lean_mkApp3(v_head_507_, v___x_564_, v___x_565_, v___x_535_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__3));
v___x_572_ = l_Lean_mkConst(v___x_571_, v___x_557_);
lean_inc(v_curCL_567_);
v_acc_573_ = l_Lean_mkApp4(v___x_572_, v___x_564_, v___x_565_, v_curCL_567_, v_ctInst_569_);
lean_inc_ref(v_acc_573_);
v___x_574_ = l_Lean_Meta_Sym_inferType___redArg(v_acc_573_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_688_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_688_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_688_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_688_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg___closed__8));
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = l_Lean_Expr_isAppOfArity(v_a_575_, v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_584_; 
lean_dec(v_a_575_);
lean_dec_ref(v_acc_573_);
lean_dec_ref(v_curHead_570_);
lean_dec(v_curCL_567_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v___x_582_ = lean_box(0);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_582_);
v___x_584_ = v___x_577_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; size_t v_sz_594_; size_t v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_577_);
v___x_586_ = l_Lean_Expr_appArg_x21(v_a_575_);
lean_dec(v_a_575_);
v___x_587_ = l_Array_extract___redArg(v_args_508_, v___x_580_, v___x_523_);
v___x_588_ = lean_box(0);
lean_inc(v___x_564_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_564_);
lean_ctor_set(v___x_589_, 1, v_curCL_567_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_curHead_570_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_acc_573_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v_sz_594_ = lean_array_size(v___x_587_);
v___x_595_ = ((size_t)0ULL);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg(v_tail_559_, v___x_587_, v_sz_594_, v___x_595_, v___x_593_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec_ref(v___x_587_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_679_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_679_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_679_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_679_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_fst_601_; 
v_fst_601_ = lean_ctor_get(v_a_597_, 0);
if (lean_obj_tag(v_fst_601_) == 0)
{
lean_object* v_snd_602_; lean_object* v_nargs_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_snd_602_ = lean_ctor_get(v_a_597_, 1);
lean_inc(v_snd_602_);
lean_dec(v_a_597_);
v_nargs_603_ = l_Lean_Expr_getAppNumArgs(v_target_506_);
lean_inc(v_nargs_603_);
v___x_604_ = lean_mk_array(v_nargs_603_, v_dummy_548_);
v___x_605_ = lean_nat_sub(v_nargs_603_, v___x_527_);
lean_dec(v_nargs_603_);
lean_inc_ref(v_target_506_);
v___x_606_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_506_, v___x_604_, v___x_605_);
v___x_607_ = lean_array_get_size(v___x_606_);
v___x_608_ = lean_nat_dec_lt(v___x_522_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v___x_606_);
lean_dec(v_snd_602_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_588_);
v___x_610_ = v___x_599_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_588_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_lt(v___x_527_, v___x_607_);
if (v___x_612_ == 0)
{
lean_object* v___x_614_; 
lean_dec_ref(v___x_606_);
lean_dec(v_snd_602_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_588_);
v___x_614_ = v___x_599_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_588_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v___x_531_, v___x_607_);
if (v___x_616_ == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v___x_606_);
lean_dec(v_snd_602_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_588_);
v___x_618_ = v___x_599_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_588_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_del_object(v___x_599_);
v___x_620_ = lean_array_fget(v___x_606_, v___x_522_);
v___x_621_ = lean_array_fget(v___x_606_, v___x_527_);
v___x_622_ = lean_array_fget(v___x_606_, v___x_531_);
lean_dec_ref(v___x_606_);
v___x_623_ = l_Lean_Expr_getAppFn(v_target_506_);
lean_dec_ref(v_target_506_);
lean_inc_n(v___x_620_, 2);
v___x_624_ = l_Lean_mkApp3(v___x_623_, v___x_620_, v___x_621_, v___x_622_);
v___x_625_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_620_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_snd_626_; lean_object* v_snd_627_; lean_object* v_a_628_; lean_object* v_fst_629_; lean_object* v_fst_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_665_; 
v_snd_626_ = lean_ctor_get(v_snd_602_, 1);
v_snd_627_ = lean_ctor_get(v_snd_626_, 1);
lean_inc(v_snd_627_);
v_a_628_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_625_, 1);
v_fst_629_ = lean_ctor_get(v_snd_602_, 0);
lean_inc(v_fst_629_);
lean_dec(v_snd_602_);
v_fst_630_ = lean_ctor_get(v_snd_627_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_snd_627_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_snd_627_, 1);
lean_dec(v_unused_666_);
v___x_632_ = v_snd_627_;
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_fst_630_);
lean_dec(v_snd_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__5));
v___x_635_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__6);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_635_);
v___x_637_ = v___x_561_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_tail_559_);
v___x_637_ = v_reuseFailAlloc_664_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 1, v___x_637_);
lean_ctor_set(v___x_632_, 0, v_a_628_);
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_628_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_663_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = l_Lean_mkConst(v___x_634_, v___x_639_);
v___x_641_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___closed__7);
v___x_642_ = l_Lean_mkAppN(v_head_507_, v_args_508_);
lean_inc_ref(v___x_624_);
lean_inc(v_fst_630_);
v___x_643_ = l_Lean_mkApp6(v___x_640_, v___x_620_, v___x_641_, v___x_642_, v_fst_630_, v___x_624_, v_fst_629_);
v___x_644_ = l_Lean_Expr_app___override(v___x_624_, v_fst_630_);
v___x_645_ = l_Lean_MVarId_replaceTargetEq(v_goal_505_, v___x_644_, v___x_643_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_a_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
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
v_a_655_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_645_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_645_);
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
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v___x_624_);
lean_dec(v___x_620_);
lean_dec(v_snd_602_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec(v_goal_505_);
v_a_667_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_625_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_625_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_675_; lean_object* v___x_677_; 
lean_inc_ref(v_fst_601_);
lean_dec(v_a_597_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v_val_675_ = lean_ctor_get(v_fst_601_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_fst_601_, 1);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_val_675_);
v___x_677_ = v___x_599_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_val_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v_a_680_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_596_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_596_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_acc_573_);
lean_dec_ref(v_curHead_570_);
lean_dec(v_curCL_567_);
lean_del_object(v___x_561_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
v_a_689_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_574_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_574_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_del_object(v___x_561_);
lean_dec(v_tail_559_);
lean_dec_ref_known(v___x_557_, 2);
lean_dec_ref(v_clArgs_552_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_519_;
}
}
}
else
{
lean_dec_ref_known(v___x_557_, 2);
lean_dec(v_tail_558_);
lean_dec_ref(v_clArgs_552_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_519_;
}
}
else
{
lean_dec(v___x_557_);
lean_dec_ref(v_clArgs_552_);
lean_dec_ref(v_head_507_);
lean_dec_ref(v_target_506_);
lean_dec(v_goal_505_);
goto v___jp_519_;
}
}
}
}
}
}
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
v___jp_519_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f___boxed(lean_object* v_goal_699_, lean_object* v_target_700_, lean_object* v_head_701_, lean_object* v_args_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(v_goal_699_, v_target_700_, v_head_701_, v_args_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec_ref(v_args_702_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(lean_object* v_tail_711_, lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___redArg(v_tail_711_, v_as_712_, v_sz_713_, v_i_714_, v_b_715_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0___boxed(lean_object* v_tail_724_, lean_object* v_as_725_, lean_object* v_sz_726_, lean_object* v_i_727_, lean_object* v_b_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_726_);
lean_dec(v_sz_726_);
v_i_boxed_737_ = lean_unbox_usize(v_i_727_);
lean_dec(v_i_727_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f_spec__0(v_tail_724_, v_as_725_, v_sz_boxed_736_, v_i_boxed_737_, v_b_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec_ref(v_as_725_);
return v_res_738_;
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
