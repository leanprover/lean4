// Lean compiler output
// Module: Lean.Meta.Sorry
// Imports: public import Lean.Data.Lsp.Utf16 public import Lean.Meta.ForEachExpr public import Lean.Meta.InferType public import Lean.Util.Recognizers
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Meta_mkSorry___closed__0 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Meta_mkSorry___closed__1 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_mkSorry___closed__2 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__2_value;
static const lean_string_object l_Lean_Meta_mkSorry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_mkSorry___closed__3 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkSorry___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSorry___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_mkSorry___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSorry___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkSorry___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_mkSorry___closed__4 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkSorry___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSorry___closed__5;
static const lean_string_object l_Lean_Meta_mkSorry___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_mkSorry___closed__6 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__6_value;
static const lean_ctor_object l_Lean_Meta_mkSorry___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSorry___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_mkSorry___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSorry___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_mkSorry___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_mkSorry___closed__7 = (const lean_object*)&l_Lean_Meta_mkSorry___closed__7_value;
static lean_once_cell_t l_Lean_Meta_mkSorry___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSorry___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SorryLabelView_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_sorry"};
static const lean_object* l_Lean_Meta_SorryLabelView_encode___closed__0 = (const lean_object*)&l_Lean_Meta_SorryLabelView_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__0 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__0_value;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__1 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__2 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__2_value;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__3 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__3_value),LEAN_SCALAR_PTR_LITERAL(242, 132, 79, 115, 245, 174, 114, 146)}};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__4 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__4_value;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__5 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__5_value;
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__5_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__6 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__7;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__8 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__8_value;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__9 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__9_value;
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__8_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__9_value),LEAN_SCALAR_PTR_LITERAL(231, 33, 22, 82, 100, 121, 126, 178)}};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__10 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__11;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__12;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__13;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__14;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__15;
static const lean_string_object l_Lean_Meta_mkLabeledSorry___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__16 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__16_value;
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__5_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_mkLabeledSorry___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__16_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_mkLabeledSorry___closed__17 = (const lean_object*)&l_Lean_Meta_mkLabeledSorry___closed__17_value;
static lean_once_cell_t l_Lean_Meta_mkLabeledSorry___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(lean_object* v_constName_1_, uint8_t v_skipRealize_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v_env_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_5_ = lean_st_ref_get(v___y_3_);
v_env_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_env_6_);
lean_dec(v___x_5_);
v___x_7_ = l_Lean_Environment_contains(v_env_6_, v_constName_1_, v_skipRealize_2_);
v___x_8_ = lean_box(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object* v_constName_10_, lean_object* v_skipRealize_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
uint8_t v_skipRealize_boxed_14_; lean_object* v_res_15_; 
v_skipRealize_boxed_14_ = lean_unbox(v_skipRealize_11_);
v_res_15_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v_constName_10_, v_skipRealize_boxed_14_, v___y_12_);
lean_dec(v___y_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(lean_object* v_constName_16_, uint8_t v_skipRealize_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v_constName_16_, v_skipRealize_17_, v___y_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(lean_object* v_constName_24_, lean_object* v_skipRealize_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
uint8_t v_skipRealize_boxed_31_; lean_object* v_res_32_; 
v_skipRealize_boxed_31_ = lean_unbox(v_skipRealize_25_);
v_res_32_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(v_constName_24_, v_skipRealize_boxed_31_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = l_Lean_Elab_abortCommandExceptionId;
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg(){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_object* v_00_u03b1_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(lean_object* v_00_u03b1_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(v_00_u03b1_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__4));
v___x_65_ = l_Lean_mkConst(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__8(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_box(0);
v___x_71_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__7));
v___x_72_ = l_Lean_mkConst(v___x_71_, v___x_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object* v_type_73_, uint8_t v_synthetic_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___x_85_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v_a_108_; uint8_t v___x_109_; uint8_t v___x_110_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_106_ = 1;
v___x_107_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_85_, v___x_106_, v_a_78_);
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_unbox(v_a_108_);
lean_dec(v_a_108_);
v___x_110_ = lean_bool_not(v___x_109_);
if (v___x_110_ == 0)
{
v___y_87_ = v_a_75_;
v___y_88_ = v_a_76_;
v___y_89_ = v_a_77_;
v___y_90_ = v_a_78_;
goto v___jp_86_;
}
else
{
lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v_type_73_);
v___x_111_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
v___jp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_inc_ref(v___y_82_);
v___x_83_ = l_Lean_mkAppB(v___y_81_, v_type_73_, v___y_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
v___jp_86_:
{
lean_object* v___x_91_; 
lean_inc_ref(v_type_73_);
v___x_91_ = l_Lean_Meta_getLevel(v_type_73_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v_a_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_Lean_mkConst(v___x_85_, v___x_94_);
if (v_synthetic_74_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_Meta_mkSorry___closed__5, &l_Lean_Meta_mkSorry___closed__5_once, _init_l_Lean_Meta_mkSorry___closed__5);
v___y_81_ = v___x_95_;
v___y_82_ = v___x_96_;
goto v___jp_80_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lean_Meta_mkSorry___closed__8, &l_Lean_Meta_mkSorry___closed__8_once, _init_l_Lean_Meta_mkSorry___closed__8);
v___y_81_ = v___x_95_;
v___y_82_ = v___x_97_;
goto v___jp_80_;
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_type_73_);
v_a_98_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_91_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_91_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* v_type_120_, lean_object* v_synthetic_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
uint8_t v_synthetic_boxed_127_; lean_object* v_res_128_; 
v_synthetic_boxed_127_ = lean_unbox(v_synthetic_121_);
v_res_128_ = l_Lean_Meta_mkSorry(v_type_120_, v_synthetic_boxed_127_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* v_view_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___y_135_; 
if (lean_obj_tag(v_view_130_) == 1)
{
lean_object* v_val_139_; lean_object* v_range_140_; lean_object* v_pos_141_; lean_object* v_endPos_142_; lean_object* v_module_143_; lean_object* v_charUtf16_144_; lean_object* v_endCharUtf16_145_; lean_object* v_line_146_; lean_object* v_column_147_; lean_object* v_line_148_; lean_object* v_column_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_val_139_ = lean_ctor_get(v_view_130_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_view_130_, 1);
v_range_140_ = lean_ctor_get(v_val_139_, 1);
lean_inc_ref(v_range_140_);
v_pos_141_ = lean_ctor_get(v_range_140_, 0);
lean_inc_ref(v_pos_141_);
v_endPos_142_ = lean_ctor_get(v_range_140_, 2);
lean_inc_ref(v_endPos_142_);
v_module_143_ = lean_ctor_get(v_val_139_, 0);
lean_inc(v_module_143_);
lean_dec(v_val_139_);
v_charUtf16_144_ = lean_ctor_get(v_range_140_, 1);
lean_inc(v_charUtf16_144_);
v_endCharUtf16_145_ = lean_ctor_get(v_range_140_, 3);
lean_inc(v_endCharUtf16_145_);
lean_dec_ref(v_range_140_);
v_line_146_ = lean_ctor_get(v_pos_141_, 0);
lean_inc(v_line_146_);
v_column_147_ = lean_ctor_get(v_pos_141_, 1);
lean_inc(v_column_147_);
lean_dec_ref(v_pos_141_);
v_line_148_ = lean_ctor_get(v_endPos_142_, 0);
lean_inc(v_line_148_);
v_column_149_ = lean_ctor_get(v_endPos_142_, 1);
lean_inc(v_column_149_);
lean_dec_ref(v_endPos_142_);
v___x_150_ = l_Lean_Name_num___override(v_module_143_, v_line_146_);
v___x_151_ = l_Lean_Name_num___override(v___x_150_, v_column_147_);
v___x_152_ = l_Lean_Name_num___override(v___x_151_, v_line_148_);
v___x_153_ = l_Lean_Name_num___override(v___x_152_, v_column_149_);
v___x_154_ = l_Lean_Name_num___override(v___x_153_, v_charUtf16_144_);
v___x_155_ = l_Lean_Name_num___override(v___x_154_, v_endCharUtf16_145_);
v___y_135_ = v___x_155_;
goto v___jp_134_;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_view_130_);
v___x_156_ = lean_box(0);
v___y_135_ = v___x_156_;
goto v___jp_134_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_137_ = l_Lean_Name_str___override(v___y_135_, v___x_136_);
v___x_138_ = l_Lean_Core_mkFreshUserName(v___x_137_, v_a_131_, v_a_132_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object* v_view_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_SorryLabelView_encode(v_view_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object* v_name_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = l_Lean_Name_hasMacroScopes(v_name_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Name_eraseMacroScopes(v_name_162_);
if (lean_obj_tag(v___x_165_) == 1)
{
lean_object* v_pre_166_; lean_object* v_str_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_pre_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_pre_166_);
v_str_167_ = lean_ctor_get(v___x_165_, 1);
lean_inc_ref(v_str_167_);
lean_dec_ref_known(v___x_165_, 2);
v___x_168_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_169_ = lean_string_dec_eq(v_str_167_, v___x_168_);
lean_dec_ref(v_str_167_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v_pre_166_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
if (lean_obj_tag(v_pre_166_) == 2)
{
lean_object* v_pre_171_; 
v_pre_171_ = lean_ctor_get(v_pre_166_, 0);
lean_inc(v_pre_171_);
if (lean_obj_tag(v_pre_171_) == 2)
{
lean_object* v_pre_172_; 
v_pre_172_ = lean_ctor_get(v_pre_171_, 0);
lean_inc(v_pre_172_);
if (lean_obj_tag(v_pre_172_) == 2)
{
lean_object* v_pre_173_; 
v_pre_173_ = lean_ctor_get(v_pre_172_, 0);
lean_inc(v_pre_173_);
if (lean_obj_tag(v_pre_173_) == 2)
{
lean_object* v_pre_174_; 
v_pre_174_ = lean_ctor_get(v_pre_173_, 0);
lean_inc(v_pre_174_);
if (lean_obj_tag(v_pre_174_) == 2)
{
lean_object* v_pre_175_; 
v_pre_175_ = lean_ctor_get(v_pre_174_, 0);
lean_inc(v_pre_175_);
if (lean_obj_tag(v_pre_175_) == 2)
{
lean_object* v_i_176_; lean_object* v_i_177_; lean_object* v_i_178_; lean_object* v_i_179_; lean_object* v_i_180_; lean_object* v_pre_181_; lean_object* v_i_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_i_176_ = lean_ctor_get(v_pre_166_, 1);
lean_inc(v_i_176_);
lean_dec_ref_known(v_pre_166_, 2);
v_i_177_ = lean_ctor_get(v_pre_171_, 1);
lean_inc(v_i_177_);
lean_dec_ref_known(v_pre_171_, 2);
v_i_178_ = lean_ctor_get(v_pre_172_, 1);
lean_inc(v_i_178_);
lean_dec_ref_known(v_pre_172_, 2);
v_i_179_ = lean_ctor_get(v_pre_173_, 1);
lean_inc(v_i_179_);
lean_dec_ref_known(v_pre_173_, 2);
v_i_180_ = lean_ctor_get(v_pre_174_, 1);
lean_inc(v_i_180_);
lean_dec_ref_known(v_pre_174_, 2);
v_pre_181_ = lean_ctor_get(v_pre_175_, 0);
lean_inc(v_pre_181_);
v_i_182_ = lean_ctor_get(v_pre_175_, 1);
lean_inc(v_i_182_);
lean_dec_ref_known(v_pre_175_, 2);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_i_182_);
lean_ctor_set(v___x_183_, 1, v_i_180_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_i_179_);
lean_ctor_set(v___x_184_, 1, v_i_178_);
v___x_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v_i_177_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
lean_ctor_set(v___x_185_, 3, v_i_176_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_pre_181_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; 
lean_dec(v_pre_175_);
lean_dec_ref_known(v_pre_174_, 2);
lean_dec_ref_known(v_pre_173_, 2);
lean_dec_ref_known(v_pre_172_, 2);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_166_, 2);
v___x_189_ = lean_box(0);
return v___x_189_;
}
}
else
{
lean_object* v___x_190_; 
lean_dec(v_pre_174_);
lean_dec_ref_known(v_pre_173_, 2);
lean_dec_ref_known(v_pre_172_, 2);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_166_, 2);
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec_ref_known(v_pre_172_, 2);
lean_dec(v_pre_173_);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_166_, 2);
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
else
{
lean_object* v___x_192_; 
lean_dec(v_pre_172_);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_166_, 2);
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec_ref_known(v_pre_166_, 2);
lean_dec(v_pre_171_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_pre_166_);
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v___x_165_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f___boxed(lean_object* v_name_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_name_196_);
lean_dec(v_name_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; lean_object* v_env_201_; lean_object* v___x_202_; lean_object* v_mainModule_203_; lean_object* v___x_204_; 
v___x_200_ = lean_st_ref_get(v___y_198_);
v_env_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_env_201_);
lean_dec(v___x_200_);
v___x_202_ = l_Lean_Environment_header(v_env_201_);
lean_dec_ref(v_env_201_);
v_mainModule_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_mainModule_203_);
lean_dec_ref(v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_mainModule_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_205_);
lean_dec(v___y_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__7(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_box(0);
v___x_232_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__6));
v___x_233_ = l_Lean_mkConst(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__11(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = l_Lean_Level_succ___override(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__12(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__13(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__12, &l_Lean_Meta_mkLabeledSorry___closed__12_once, _init_l_Lean_Meta_mkLabeledSorry___closed__12);
v___x_245_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__14(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__13, &l_Lean_Meta_mkLabeledSorry___closed__13_once, _init_l_Lean_Meta_mkLabeledSorry___closed__13);
v___x_248_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_249_ = l_Lean_mkConst(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__15(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_box(0);
v___x_251_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_252_ = l_Lean_mkConst(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__18(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* v_type_260_, uint8_t v_synthetic_261_, uint8_t v_unique_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; lean_object* v_tag_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v_a_373_; uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_371_ = 1;
v___x_372_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_268_, v___x_371_, v_a_266_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref(v___x_372_);
v___x_374_ = lean_unbox(v_a_373_);
lean_dec(v_a_373_);
v___x_375_ = lean_bool_not(v___x_374_);
if (v___x_375_ == 0)
{
v___y_326_ = v_a_263_;
v___y_327_ = v_a_264_;
v___y_328_ = v_a_265_;
v___y_329_ = v_a_266_;
goto v___jp_325_;
}
else
{
lean_object* v___x_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_type_260_);
v___x_376_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_269_:
{
if (v_unique_262_ == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_275_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_276_ = 0;
v___x_277_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__7, &l_Lean_Meta_mkLabeledSorry___closed__7_once, _init_l_Lean_Meta_mkLabeledSorry___closed__7);
v___x_278_ = l_Lean_mkForall(v___x_275_, v___x_276_, v___x_277_, v_type_260_);
v___x_279_ = l_Lean_Meta_mkSorry(v___x_278_, v_synthetic_261_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_293_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_293_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__14, &l_Lean_Meta_mkLabeledSorry___closed__14_once, _init_l_Lean_Meta_mkLabeledSorry___closed__14);
v___x_285_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_286_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__18, &l_Lean_Meta_mkLabeledSorry___closed__18_once, _init_l_Lean_Meta_mkLabeledSorry___closed__18);
v___x_287_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_270_);
v___x_288_ = l_Lean_mkApp4(v___x_284_, v___x_277_, v___x_285_, v___x_286_, v___x_287_);
v___x_289_ = l_Lean_Expr_app___override(v_a_280_, v___x_288_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_289_);
v___x_291_ = v___x_282_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_dec(v_tag_270_);
return v___x_279_;
}
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_295_ = 0;
v___x_296_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_297_ = l_Lean_mkForall(v___x_294_, v___x_295_, v___x_296_, v_type_260_);
v___x_298_ = l_Lean_Meta_mkSorry(v___x_297_, v_synthetic_261_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_308_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_308_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_303_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_270_);
v___x_304_ = l_Lean_Expr_app___override(v_a_299_, v___x_303_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_304_);
v___x_306_ = v___x_301_;
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
else
{
lean_dec(v_tag_270_);
return v___x_298_;
}
}
}
v___jp_309_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(0);
v___x_315_ = l_Lean_Meta_SorryLabelView_encode(v___x_314_, v___y_312_, v___y_313_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v_tag_270_ = v_a_316_;
v___y_271_ = v___y_310_;
v___y_272_ = v___y_311_;
v___y_273_ = v___y_312_;
v___y_274_ = v___y_313_;
goto v___jp_269_;
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_type_260_);
v_a_317_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_315_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
v___jp_325_:
{
lean_object* v_fileMap_330_; lean_object* v_ref_331_; uint8_t v___x_332_; lean_object* v___x_333_; 
v_fileMap_330_ = lean_ctor_get(v___y_328_, 1);
v_ref_331_ = lean_ctor_get(v___y_328_, 5);
v___x_332_ = 0;
v___x_333_ = l_Lean_Syntax_getPos_x3f(v_ref_331_, v___x_332_);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_335_; 
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = l_Lean_Syntax_getTailPos_x3f(v_ref_331_, v___x_332_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_370_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_370_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_370_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_370_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_character_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_character_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_368_; 
v___x_340_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_329_);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
lean_inc_ref_n(v_fileMap_330_, 4);
v___x_342_ = l_Lean_FileMap_toPosition(v_fileMap_330_, v_val_334_);
v___x_343_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_330_, v_val_334_);
lean_dec(v_val_334_);
v_character_344_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_character_344_);
lean_dec_ref(v___x_343_);
v___x_345_ = l_Lean_FileMap_toPosition(v_fileMap_330_, v_val_336_);
v___x_346_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_330_, v_val_336_);
lean_dec(v_val_336_);
v_character_347_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_346_, 0);
lean_dec(v_unused_369_);
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_368_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_character_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_368_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_342_);
lean_ctor_set(v___x_351_, 1, v_character_344_);
lean_ctor_set(v___x_351_, 2, v___x_345_);
lean_ctor_set(v___x_351_, 3, v_character_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_351_);
lean_ctor_set(v___x_349_, 0, v_a_341_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_367_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_353_);
v___x_355_ = v___x_338_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_366_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Meta_SorryLabelView_encode(v___x_355_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v_tag_270_ = v_a_357_;
v___y_271_ = v___y_326_;
v___y_272_ = v___y_327_;
v___y_273_ = v___y_328_;
v___y_274_ = v___y_329_;
goto v___jp_269_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_type_260_);
v_a_358_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_356_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
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
lean_dec(v___x_335_);
lean_dec(v_val_334_);
v___y_310_ = v___y_326_;
v___y_311_ = v___y_327_;
v___y_312_ = v___y_328_;
v___y_313_ = v___y_329_;
goto v___jp_309_;
}
}
else
{
lean_dec(v___x_333_);
v___y_310_ = v___y_326_;
v___y_311_ = v___y_327_;
v___y_312_ = v___y_328_;
v___y_313_ = v___y_329_;
goto v___jp_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* v_type_385_, lean_object* v_synthetic_386_, lean_object* v_unique_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
uint8_t v_synthetic_boxed_393_; uint8_t v_unique_boxed_394_; lean_object* v_res_395_; 
v_synthetic_boxed_393_ = lean_unbox(v_synthetic_386_);
v_unique_boxed_394_ = lean_unbox(v_unique_387_);
v_res_395_ = l_Lean_Meta_mkLabeledSorry(v_type_385_, v_synthetic_boxed_393_, v_unique_boxed_394_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object* v_e_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_398_ = l_Lean_Expr_isAppOf(v_e_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_Expr_getAppNumArgs(v_e_396_);
v___x_401_ = lean_unsigned_to_nat(3u);
v___x_402_ = lean_nat_dec_le(v___x_401_, v___x_400_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = lean_unsigned_to_nat(2u);
v___x_405_ = lean_nat_sub(v___x_400_, v___x_404_);
lean_dec(v___x_400_);
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_sub(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
v___x_408_ = l_Lean_Expr_getRevArg_x21(v_e_396_, v___x_407_);
lean_inc_ref(v___x_408_);
v___x_409_ = l_Lean_Expr_name_x3f(v___x_408_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; 
lean_dec_ref(v___x_408_);
v_val_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_410_);
lean_dec(v_val_410_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
lean_dec(v___x_409_);
v___x_412_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_413_ = lean_unsigned_to_nat(4u);
v___x_414_ = l_Lean_Expr_isAppOfArity(v___x_408_, v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v___x_408_);
v___x_415_ = lean_box(0);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_416_ = l_Lean_Expr_appFn_x21(v___x_408_);
v___x_417_ = l_Lean_Expr_appArg_x21(v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = l_Lean_Expr_isAppOfArity(v___x_417_, v___x_418_, v___x_419_);
lean_dec_ref(v___x_417_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec_ref(v___x_408_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = l_Lean_Expr_appArg_x21(v___x_408_);
lean_dec_ref(v___x_408_);
v___x_423_ = l_Lean_Expr_name_x3f(v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_426_; 
v_val_425_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v___x_423_, 1);
v___x_426_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_425_);
lean_dec(v_val_425_);
return v___x_426_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object* v_e_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_427_);
lean_dec_ref(v_e_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object* v_e_429_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Expr_isSorry(v_e_429_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = lean_box(0);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_429_);
if (lean_obj_tag(v___x_438_) == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_438_, 0);
lean_dec(v_unused_450_);
v___x_440_ = v___x_438_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___x_438_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
if (v___x_436_ == 0)
{
lean_del_object(v___x_440_);
goto v___jp_430_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_442_ = l_Lean_Expr_getAppNumArgs(v_e_429_);
v___x_443_ = lean_unsigned_to_nat(3u);
v___x_444_ = lean_nat_sub(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
v___x_445_ = l_Lean_Expr_getBoundedAppFn(v___x_444_, v_e_429_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_445_);
v___x_447_ = v___x_440_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_431_ = l_Lean_Expr_getAppNumArgs(v_e_429_);
v___x_432_ = lean_unsigned_to_nat(2u);
v___x_433_ = lean_nat_sub(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
v___x_434_ = l_Lean_Expr_getBoundedAppFn(v___x_433_, v_e_429_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object* v_e_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Expr_getSorry_x3f(v_e_451_);
lean_dec_ref(v_e_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object* v_toPure_453_, lean_object* v_____r_454_){
_start:
{
uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = 0;
v___x_456_ = lean_box(v___x_455_);
v___x_457_ = lean_apply_2(v_toPure_453_, lean_box(0), v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object* v_fn_458_, lean_object* v_toBind_459_, lean_object* v___f_460_, lean_object* v_toPure_461_, lean_object* v_e_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Expr_getSorry_x3f(v_e_462_);
if (lean_obj_tag(v___x_463_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_toPure_461_);
v_val_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_apply_1(v_fn_458_, v_val_464_);
v___x_466_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_465_, v___f_460_);
return v___x_466_;
}
else
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_463_);
lean_dec(v___f_460_);
lean_dec(v_toBind_459_);
lean_dec(v_fn_458_);
v___x_467_ = 1;
v___x_468_ = lean_box(v___x_467_);
v___x_469_ = lean_apply_2(v_toPure_461_, lean_box(0), v___x_468_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object* v_fn_470_, lean_object* v_toBind_471_, lean_object* v___f_472_, lean_object* v_toPure_473_, lean_object* v_e_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_forEachSorryM___redArg___lam__1(v_fn_470_, v_toBind_471_, v___f_472_, v_toPure_473_, v_e_474_);
lean_dec_ref(v_e_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_input_479_, lean_object* v_fn_480_){
_start:
{
lean_object* v_toApplicative_481_; lean_object* v_toBind_482_; lean_object* v_toPure_483_; lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___x_486_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_476_, 0);
v_toBind_482_ = lean_ctor_get(v_inst_476_, 1);
v_toPure_483_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc_n(v_toPure_483_, 2);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_484_, 0, v_toPure_483_);
lean_inc(v_toBind_482_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_485_, 0, v_fn_480_);
lean_closure_set(v___f_485_, 1, v_toBind_482_);
lean_closure_set(v___f_485_, 2, v___f_484_);
lean_closure_set(v___f_485_, 3, v_toPure_483_);
v___x_486_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_476_, v_inst_477_, v_inst_478_, v_input_479_, v___f_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object* v_m_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_input_491_, lean_object* v_fn_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_input_491_, v_fn_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_fn_497_, lean_object* v_x_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_494_, v_inst_495_, v_inst_496_, v_a_499_, v_fn_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_decl_504_, lean_object* v_fn_505_){
_start:
{
lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc_ref(v_inst_501_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Declaration_forEachSorryM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_506_, 0, v_inst_501_);
lean_closure_set(v___f_506_, 1, v_inst_502_);
lean_closure_set(v___f_506_, 2, v_inst_503_);
lean_closure_set(v___f_506_, 3, v_fn_505_);
v___x_507_ = lean_box(0);
v___x_508_ = l_Lean_Declaration_foldExprM___redArg(v_inst_501_, v_decl_504_, v___f_506_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object* v_m_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_decl_513_, lean_object* v_fn_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Declaration_forEachSorryM___redArg(v_inst_510_, v_inst_511_, v_inst_512_, v_decl_513_, v_fn_514_);
return v___x_515_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sorry(builtin);
}
#ifdef __cplusplus
}
#endif
