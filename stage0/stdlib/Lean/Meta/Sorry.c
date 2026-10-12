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
lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(lean_object* v_constName_1_, uint8_t v_skipRealize_2_, lean_object* v___y_3_){
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
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1_ = stack[0].m_obj;
uint8_t v_skipRealize_2_ = stack[1].m_num;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v_constName_1_, v_skipRealize_2_, v___y_3_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object* v_constName_11_, lean_object* v_skipRealize_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
uint8_t v_skipRealize_boxed_15_; lean_object* v_res_16_; 
v_skipRealize_boxed_15_ = lean_unbox(v_skipRealize_12_);
v_res_16_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v_constName_11_, v_skipRealize_boxed_15_, v___y_13_);
lean_dec(v___y_13_);
return v_res_16_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(lean_object* v_constName_17_, uint8_t v_skipRealize_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v_constName_17_, v_skipRealize_18_, v___y_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_17_ = stack[0].m_obj;
uint8_t v_skipRealize_18_ = stack[1].m_num;
lean_object* v___y_19_ = stack[2].m_obj;
lean_object* v___y_20_ = stack[3].m_obj;
lean_object* v___y_21_ = stack[4].m_obj;
lean_object* v___y_22_ = stack[5].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(v_constName_17_, v_skipRealize_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(lean_object* v_constName_26_, lean_object* v_skipRealize_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
uint8_t v_skipRealize_boxed_33_; lean_object* v_res_34_; 
v_skipRealize_boxed_33_ = lean_unbox(v_skipRealize_27_);
v_res_34_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(v_constName_26_, v_skipRealize_boxed_33_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_34_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_box(0);
v___x_36_ = l_Lean_Elab_abortCommandExceptionId;
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg(){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_41_;
v_res_41_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return v_res_43_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_object* v_00_u03b1_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return v___x_50_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_45_ = stack[1].m_obj;
lean_object* v___y_46_ = stack[2].m_obj;
lean_object* v___y_47_ = stack[3].m_obj;
lean_object* v___y_48_ = stack[4].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_box(0), v___y_45_, v___y_46_, v___y_47_, v___y_48_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(lean_object* v_00_u03b1_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(v_00_u03b1_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__5(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__4));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__8(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_box(0);
v___x_75_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__7));
v___x_76_ = l_Lean_mkConst(v___x_75_, v___x_74_);
return v___x_76_;
}
}
lean_object* l_Lean_Meta_mkSorry(lean_object* v_type_77_, uint8_t v_synthetic_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___x_89_; lean_object* v___y_91_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_94_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v_a_112_; uint8_t v___x_113_; 
v___x_89_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_110_ = 1;
v___x_111_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_89_, v___x_110_, v_a_82_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v___x_111_);
v___x_113_ = lean_unbox(v_a_112_);
lean_dec(v_a_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v_type_77_);
v___x_114_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
v___y_91_ = v_a_79_;
v___y_92_ = v_a_80_;
v___y_93_ = v_a_81_;
v___y_94_ = v_a_82_;
goto v___jp_90_;
}
v___jp_84_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_inc_ref(v___y_86_);
v___x_87_ = l_Lean_mkAppB(v___y_85_, v_type_77_, v___y_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
v___jp_90_:
{
lean_object* v___x_95_; 
lean_inc_ref(v_type_77_);
v___x_95_ = l_Lean_Meta_getLevel(v_type_77_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = lean_box(0);
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v_a_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = l_Lean_mkConst(v___x_89_, v___x_98_);
if (v_synthetic_78_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_mkSorry___closed__5, &l_Lean_Meta_mkSorry___closed__5_once, _init_l_Lean_Meta_mkSorry___closed__5);
v___y_85_ = v___x_99_;
v___y_86_ = v___x_100_;
goto v___jp_84_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Meta_mkSorry___closed__8, &l_Lean_Meta_mkSorry___closed__8_once, _init_l_Lean_Meta_mkSorry___closed__8);
v___y_85_ = v___x_99_;
v___y_86_ = v___x_101_;
goto v___jp_84_;
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_type_77_);
v_a_102_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_95_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_95_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_77_ = stack[0].m_obj;
uint8_t v_synthetic_78_ = stack[1].m_num;
lean_object* v_a_79_ = stack[2].m_obj;
lean_object* v_a_80_ = stack[3].m_obj;
lean_object* v_a_81_ = stack[4].m_obj;
lean_object* v_a_82_ = stack[5].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Meta_mkSorry(v_type_77_, v_synthetic_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* v_type_124_, lean_object* v_synthetic_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
uint8_t v_synthetic_boxed_131_; lean_object* v_res_132_; 
v_synthetic_boxed_131_ = lean_unbox(v_synthetic_125_);
v_res_132_ = l_Lean_Meta_mkSorry(v_type_124_, v_synthetic_boxed_131_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_132_;
}
}
lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* v_view_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___y_139_; 
if (lean_obj_tag(v_view_134_) == 1)
{
lean_object* v_val_143_; lean_object* v_range_144_; lean_object* v_pos_145_; lean_object* v_endPos_146_; lean_object* v_module_147_; lean_object* v_charUtf16_148_; lean_object* v_endCharUtf16_149_; lean_object* v_line_150_; lean_object* v_column_151_; lean_object* v_line_152_; lean_object* v_column_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_val_143_ = lean_ctor_get(v_view_134_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v_view_134_, 1);
v_range_144_ = lean_ctor_get(v_val_143_, 1);
lean_inc_ref(v_range_144_);
v_pos_145_ = lean_ctor_get(v_range_144_, 0);
lean_inc_ref(v_pos_145_);
v_endPos_146_ = lean_ctor_get(v_range_144_, 2);
lean_inc_ref(v_endPos_146_);
v_module_147_ = lean_ctor_get(v_val_143_, 0);
lean_inc(v_module_147_);
lean_dec(v_val_143_);
v_charUtf16_148_ = lean_ctor_get(v_range_144_, 1);
lean_inc(v_charUtf16_148_);
v_endCharUtf16_149_ = lean_ctor_get(v_range_144_, 3);
lean_inc(v_endCharUtf16_149_);
lean_dec_ref(v_range_144_);
v_line_150_ = lean_ctor_get(v_pos_145_, 0);
lean_inc(v_line_150_);
v_column_151_ = lean_ctor_get(v_pos_145_, 1);
lean_inc(v_column_151_);
lean_dec_ref(v_pos_145_);
v_line_152_ = lean_ctor_get(v_endPos_146_, 0);
lean_inc(v_line_152_);
v_column_153_ = lean_ctor_get(v_endPos_146_, 1);
lean_inc(v_column_153_);
lean_dec_ref(v_endPos_146_);
v___x_154_ = l_Lean_Name_num___override(v_module_147_, v_line_150_);
v___x_155_ = l_Lean_Name_num___override(v___x_154_, v_column_151_);
v___x_156_ = l_Lean_Name_num___override(v___x_155_, v_line_152_);
v___x_157_ = l_Lean_Name_num___override(v___x_156_, v_column_153_);
v___x_158_ = l_Lean_Name_num___override(v___x_157_, v_charUtf16_148_);
v___x_159_ = l_Lean_Name_num___override(v___x_158_, v_endCharUtf16_149_);
v___y_139_ = v___x_159_;
goto v___jp_138_;
}
else
{
lean_object* v___x_160_; 
lean_dec(v_view_134_);
v___x_160_ = lean_box(0);
v___y_139_ = v___x_160_;
goto v___jp_138_;
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_141_ = l_Lean_Name_str___override(v___y_139_, v___x_140_);
v___x_142_ = l_Lean_Core_mkFreshUserName(v___x_141_, v_a_135_, v_a_136_);
return v___x_142_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_SorryLabelView_encode_0interp(lean_interpreter_value* stack)
{
lean_object* v_view_134_ = stack[0].m_obj;
lean_object* v_a_135_ = stack[1].m_obj;
lean_object* v_a_136_ = stack[2].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_Meta_SorryLabelView_encode(v_view_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object* v_view_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_SorryLabelView_encode(v_view_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object* v_name_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Name_hasMacroScopes(v_name_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Name_eraseMacroScopes(v_name_167_);
if (lean_obj_tag(v___x_170_) == 1)
{
lean_object* v_pre_171_; lean_object* v_str_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_pre_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_pre_171_);
v_str_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc_ref(v_str_172_);
lean_dec_ref_known(v___x_170_, 2);
v___x_173_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_174_ = lean_string_dec_eq(v_str_172_, v___x_173_);
lean_dec_ref(v_str_172_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_pre_171_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
if (lean_obj_tag(v_pre_171_) == 2)
{
lean_object* v_pre_176_; 
v_pre_176_ = lean_ctor_get(v_pre_171_, 0);
lean_inc(v_pre_176_);
if (lean_obj_tag(v_pre_176_) == 2)
{
lean_object* v_pre_177_; 
v_pre_177_ = lean_ctor_get(v_pre_176_, 0);
lean_inc(v_pre_177_);
if (lean_obj_tag(v_pre_177_) == 2)
{
lean_object* v_pre_178_; 
v_pre_178_ = lean_ctor_get(v_pre_177_, 0);
lean_inc(v_pre_178_);
if (lean_obj_tag(v_pre_178_) == 2)
{
lean_object* v_pre_179_; 
v_pre_179_ = lean_ctor_get(v_pre_178_, 0);
lean_inc(v_pre_179_);
if (lean_obj_tag(v_pre_179_) == 2)
{
lean_object* v_pre_180_; 
v_pre_180_ = lean_ctor_get(v_pre_179_, 0);
lean_inc(v_pre_180_);
if (lean_obj_tag(v_pre_180_) == 2)
{
lean_object* v_i_181_; lean_object* v_i_182_; lean_object* v_i_183_; lean_object* v_i_184_; lean_object* v_i_185_; lean_object* v_pre_186_; lean_object* v_i_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_i_181_ = lean_ctor_get(v_pre_171_, 1);
lean_inc(v_i_181_);
lean_dec_ref_known(v_pre_171_, 2);
v_i_182_ = lean_ctor_get(v_pre_176_, 1);
lean_inc(v_i_182_);
lean_dec_ref_known(v_pre_176_, 2);
v_i_183_ = lean_ctor_get(v_pre_177_, 1);
lean_inc(v_i_183_);
lean_dec_ref_known(v_pre_177_, 2);
v_i_184_ = lean_ctor_get(v_pre_178_, 1);
lean_inc(v_i_184_);
lean_dec_ref_known(v_pre_178_, 2);
v_i_185_ = lean_ctor_get(v_pre_179_, 1);
lean_inc(v_i_185_);
lean_dec_ref_known(v_pre_179_, 2);
v_pre_186_ = lean_ctor_get(v_pre_180_, 0);
lean_inc(v_pre_186_);
v_i_187_ = lean_ctor_get(v_pre_180_, 1);
lean_inc(v_i_187_);
lean_dec_ref_known(v_pre_180_, 2);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_i_187_);
lean_ctor_set(v___x_188_, 1, v_i_185_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_i_184_);
lean_ctor_set(v___x_189_, 1, v_i_183_);
v___x_190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v_i_182_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
lean_ctor_set(v___x_190_, 3, v_i_181_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_pre_186_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
lean_dec_ref_known(v_pre_179_, 2);
lean_dec(v_pre_180_);
lean_dec_ref_known(v_pre_178_, 2);
lean_dec_ref_known(v_pre_177_, 2);
lean_dec_ref_known(v_pre_176_, 2);
lean_dec_ref_known(v_pre_171_, 2);
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_pre_179_);
lean_dec_ref_known(v_pre_178_, 2);
lean_dec_ref_known(v_pre_177_, 2);
lean_dec_ref_known(v_pre_176_, 2);
lean_dec_ref_known(v_pre_171_, 2);
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v_pre_178_);
lean_dec_ref_known(v_pre_177_, 2);
lean_dec_ref_known(v_pre_176_, 2);
lean_dec_ref_known(v_pre_171_, 2);
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec(v_pre_177_);
lean_dec_ref_known(v_pre_176_, 2);
lean_dec_ref_known(v_pre_171_, 2);
v___x_197_ = lean_box(0);
return v___x_197_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref_known(v_pre_171_, 2);
lean_dec(v_pre_176_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_pre_171_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
}
else
{
lean_object* v___x_200_; 
lean_dec(v___x_170_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f___boxed(lean_object* v_name_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_name_201_);
lean_dec(v_name_201_);
return v_res_202_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_env_206_; lean_object* v___x_207_; lean_object* v_mainModule_208_; lean_object* v___x_209_; 
v___x_205_ = lean_st_ref_get(v___y_203_);
v_env_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc_ref(v_env_206_);
lean_dec(v___x_205_);
v___x_207_ = l_Lean_Environment_header(v_env_206_);
lean_dec_ref(v_env_206_);
v_mainModule_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_mainModule_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_mainModule_208_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_203_ = stack[0].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_203_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_211_);
lean_dec(v___y_211_);
return v_res_213_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_214_ = stack[0].m_obj;
lean_object* v___y_215_ = stack[1].m_obj;
lean_object* v___y_216_ = stack[2].m_obj;
lean_object* v___y_217_ = stack[3].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__7(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_box(0);
v___x_239_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__6));
v___x_240_ = l_Lean_mkConst(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__11(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_Level_succ___override(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__12(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__13(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__12, &l_Lean_Meta_mkLabeledSorry___closed__12_once, _init_l_Lean_Meta_mkLabeledSorry___closed__12);
v___x_252_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__14(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__13, &l_Lean_Meta_mkLabeledSorry___closed__13_once, _init_l_Lean_Meta_mkLabeledSorry___closed__13);
v___x_255_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_256_ = l_Lean_mkConst(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__15(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__18(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_266_ = l_Lean_mkConst(v___x_265_, v___x_264_);
return v___x_266_;
}
}
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* v_type_267_, uint8_t v_synthetic_268_, uint8_t v_unique_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v_tag_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v_a_381_; uint8_t v___x_382_; 
v___x_275_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_379_ = 1;
v___x_380_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_275_, v___x_379_, v_a_273_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v___x_382_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v_type_267_);
v___x_383_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
v___y_333_ = v_a_270_;
v___y_334_ = v_a_271_;
v___y_335_ = v_a_272_;
v___y_336_ = v_a_273_;
goto v___jp_332_;
}
v___jp_276_:
{
if (v_unique_269_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_283_ = 0;
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__7, &l_Lean_Meta_mkLabeledSorry___closed__7_once, _init_l_Lean_Meta_mkLabeledSorry___closed__7);
v___x_285_ = l_Lean_mkForall(v___x_282_, v___x_283_, v___x_284_, v_type_267_);
v___x_286_ = l_Lean_Meta_mkSorry(v___x_285_, v_synthetic_268_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_300_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_300_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_291_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__14, &l_Lean_Meta_mkLabeledSorry___closed__14_once, _init_l_Lean_Meta_mkLabeledSorry___closed__14);
v___x_292_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_293_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__18, &l_Lean_Meta_mkLabeledSorry___closed__18_once, _init_l_Lean_Meta_mkLabeledSorry___closed__18);
v___x_294_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_277_);
v___x_295_ = l_Lean_mkApp4(v___x_291_, v___x_284_, v___x_292_, v___x_293_, v___x_294_);
v___x_296_ = l_Lean_Expr_app___override(v_a_287_, v___x_295_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_296_);
v___x_298_ = v___x_289_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_dec(v_tag_277_);
return v___x_286_;
}
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_302_ = 0;
v___x_303_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_304_ = l_Lean_mkForall(v___x_301_, v___x_302_, v___x_303_, v_type_267_);
v___x_305_ = l_Lean_Meta_mkSorry(v___x_304_, v_synthetic_268_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_315_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_315_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_277_);
v___x_311_ = l_Lean_Expr_app___override(v_a_306_, v___x_310_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_dec(v_tag_277_);
return v___x_305_;
}
}
}
v___jp_316_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(0);
v___x_322_ = l_Lean_Meta_SorryLabelView_encode(v___x_321_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v_tag_277_ = v_a_323_;
v___y_278_ = v___y_317_;
v___y_279_ = v___y_318_;
v___y_280_ = v___y_319_;
v___y_281_ = v___y_320_;
goto v___jp_276_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_type_267_);
v_a_324_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_322_);
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
lean_object* v_toCold_337_; lean_object* v_ref_338_; uint8_t v___x_339_; lean_object* v___x_340_; 
v_toCold_337_ = lean_ctor_get(v___y_335_, 0);
v_ref_338_ = lean_ctor_get(v___y_335_, 2);
v___x_339_ = 0;
v___x_340_ = l_Lean_Syntax_getPos_x3f(v_ref_338_, v___x_339_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v_val_341_; lean_object* v___x_342_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = l_Lean_Syntax_getTailPos_x3f(v_ref_338_, v___x_339_);
if (lean_obj_tag(v___x_342_) == 1)
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_378_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_378_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_378_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_378_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_fileMap_347_; lean_object* v___x_348_; lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_character_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_character_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_376_; 
v_fileMap_347_ = lean_ctor_get(v_toCold_337_, 1);
v___x_348_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_336_);
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref(v___x_348_);
lean_inc_ref_n(v_fileMap_347_, 4);
v___x_350_ = l_Lean_FileMap_toPosition(v_fileMap_347_, v_val_341_);
v___x_351_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_347_, v_val_341_);
lean_dec(v_val_341_);
v_character_352_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_character_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = l_Lean_FileMap_toPosition(v_fileMap_347_, v_val_343_);
v___x_354_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_347_, v_val_343_);
lean_dec(v_val_343_);
v_character_355_ = lean_ctor_get(v___x_354_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_377_);
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_376_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_character_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_376_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_359_, 0, v___x_350_);
lean_ctor_set(v___x_359_, 1, v_character_352_);
lean_ctor_set(v___x_359_, 2, v___x_353_);
lean_ctor_set(v___x_359_, 3, v_character_355_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_359_);
lean_ctor_set(v___x_357_, 0, v_a_349_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_349_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_375_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_361_);
v___x_363_ = v___x_345_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_374_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_SorryLabelView_encode(v___x_363_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v_tag_277_ = v_a_365_;
v___y_278_ = v___y_333_;
v___y_279_ = v___y_334_;
v___y_280_ = v___y_335_;
v___y_281_ = v___y_336_;
goto v___jp_276_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_type_267_);
v_a_366_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
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
lean_dec(v___x_342_);
lean_dec(v_val_341_);
v___y_317_ = v___y_333_;
v___y_318_ = v___y_334_;
v___y_319_ = v___y_335_;
v___y_320_ = v___y_336_;
goto v___jp_316_;
}
}
else
{
lean_dec(v___x_340_);
v___y_317_ = v___y_333_;
v___y_318_ = v___y_334_;
v___y_319_ = v___y_335_;
v___y_320_ = v___y_336_;
goto v___jp_316_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkLabeledSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_267_ = stack[0].m_obj;
uint8_t v_synthetic_268_ = stack[1].m_num;
uint8_t v_unique_269_ = stack[2].m_num;
lean_object* v_a_270_ = stack[3].m_obj;
lean_object* v_a_271_ = stack[4].m_obj;
lean_object* v_a_272_ = stack[5].m_obj;
lean_object* v_a_273_ = stack[6].m_obj;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Meta_mkLabeledSorry(v_type_267_, v_synthetic_268_, v_unique_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* v_type_393_, lean_object* v_synthetic_394_, lean_object* v_unique_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_synthetic_boxed_401_; uint8_t v_unique_boxed_402_; lean_object* v_res_403_; 
v_synthetic_boxed_401_ = lean_unbox(v_synthetic_394_);
v_unique_boxed_402_ = lean_unbox(v_unique_395_);
v_res_403_ = l_Lean_Meta_mkLabeledSorry(v_type_393_, v_synthetic_boxed_401_, v_unique_boxed_402_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object* v_e_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_406_ = l_Lean_Expr_isAppOf(v_e_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = l_Lean_Expr_getAppNumArgs(v_e_404_);
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = lean_nat_dec_le(v___x_409_, v___x_408_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = lean_unsigned_to_nat(2u);
v___x_413_ = lean_nat_sub(v___x_408_, v___x_412_);
lean_dec(v___x_408_);
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_sub(v___x_413_, v___x_414_);
lean_dec(v___x_413_);
v___x_416_ = l_Lean_Expr_getRevArg_x21(v_e_404_, v___x_415_);
lean_inc_ref(v___x_416_);
v___x_417_ = l_Lean_Expr_name_x3f(v___x_416_);
if (lean_obj_tag(v___x_417_) == 1)
{
lean_object* v_val_418_; lean_object* v___x_419_; 
lean_dec_ref(v___x_416_);
v_val_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v___x_417_, 1);
v___x_419_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_418_);
lean_dec(v_val_418_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
lean_dec(v___x_417_);
v___x_420_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_421_ = lean_unsigned_to_nat(4u);
v___x_422_ = l_Lean_Expr_isAppOfArity(v___x_416_, v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v___x_416_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_424_ = l_Lean_Expr_appFn_x21(v___x_416_);
v___x_425_ = l_Lean_Expr_appArg_x21(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = l_Lean_Expr_isAppOfArity(v___x_425_, v___x_426_, v___x_427_);
lean_dec_ref(v___x_425_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec_ref(v___x_416_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = l_Lean_Expr_appArg_x21(v___x_416_);
lean_dec_ref(v___x_416_);
v___x_431_ = l_Lean_Expr_name_x3f(v___x_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_box(0);
return v___x_432_;
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
v_val_433_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_431_, 1);
v___x_434_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_433_);
lean_dec(v_val_433_);
return v___x_434_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object* v_e_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_435_);
lean_dec_ref(v_e_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object* v_e_437_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_Expr_isSorry(v_e_437_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_437_);
if (lean_obj_tag(v___x_446_) == 0)
{
goto v___jp_438_;
}
else
{
lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_446_, 0);
lean_dec(v_unused_458_);
v___x_448_ = v___x_446_;
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
else
{
lean_dec(v___x_446_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
if (v___x_444_ == 0)
{
lean_del_object(v___x_448_);
goto v___jp_438_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_450_ = l_Lean_Expr_getAppNumArgs(v_e_437_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = lean_nat_sub(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
v___x_453_ = l_Lean_Expr_getBoundedAppFn(v___x_452_, v_e_437_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_453_);
v___x_455_ = v___x_448_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
v___jp_438_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_439_ = l_Lean_Expr_getAppNumArgs(v_e_437_);
v___x_440_ = lean_unsigned_to_nat(2u);
v___x_441_ = lean_nat_sub(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
v___x_442_ = l_Lean_Expr_getBoundedAppFn(v___x_441_, v_e_437_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object* v_e_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Expr_getSorry_x3f(v_e_459_);
lean_dec_ref(v_e_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object* v_toPure_461_, lean_object* v_____r_462_){
_start:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = 0;
v___x_464_ = lean_box(v___x_463_);
v___x_465_ = lean_apply_2(v_toPure_461_, lean_box(0), v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object* v_fn_466_, lean_object* v_toBind_467_, lean_object* v___f_468_, lean_object* v_toPure_469_, lean_object* v_e_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Expr_getSorry_x3f(v_e_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_toPure_469_);
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = lean_apply_1(v_fn_466_, v_val_472_);
v___x_474_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_473_, v___f_468_);
return v___x_474_;
}
else
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v___x_471_);
lean_dec(v___f_468_);
lean_dec(v_toBind_467_);
lean_dec(v_fn_466_);
v___x_475_ = 1;
v___x_476_ = lean_box(v___x_475_);
v___x_477_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object* v_fn_478_, lean_object* v_toBind_479_, lean_object* v___f_480_, lean_object* v_toPure_481_, lean_object* v_e_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_forEachSorryM___redArg___lam__1(v_fn_478_, v_toBind_479_, v___f_480_, v_toPure_481_, v_e_482_);
lean_dec_ref(v_e_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_input_487_, lean_object* v_fn_488_){
_start:
{
lean_object* v_toApplicative_489_; lean_object* v_toBind_490_; lean_object* v_toPure_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_toApplicative_489_ = lean_ctor_get(v_inst_484_, 0);
v_toBind_490_ = lean_ctor_get(v_inst_484_, 1);
v_toPure_491_ = lean_ctor_get(v_toApplicative_489_, 1);
lean_inc_n(v_toPure_491_, 2);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_492_, 0, v_toPure_491_);
lean_inc(v_toBind_490_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_493_, 0, v_fn_488_);
lean_closure_set(v___f_493_, 1, v_toBind_490_);
lean_closure_set(v___f_493_, 2, v___f_492_);
lean_closure_set(v___f_493_, 3, v_toPure_491_);
v___x_494_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_484_, v_inst_485_, v_inst_486_, v_input_487_, v___f_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_input_499_, lean_object* v_fn_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_496_, v_inst_497_, v_inst_498_, v_input_499_, v_fn_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_fn_505_, lean_object* v_x_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_502_, v_inst_503_, v_inst_504_, v_a_507_, v_fn_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_decl_512_, lean_object* v_fn_513_){
_start:
{
lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_inc_ref(v_inst_509_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Declaration_forEachSorryM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_514_, 0, v_inst_509_);
lean_closure_set(v___f_514_, 1, v_inst_510_);
lean_closure_set(v___f_514_, 2, v_inst_511_);
lean_closure_set(v___f_514_, 3, v_fn_513_);
v___x_515_ = lean_box(0);
v___x_516_ = l_Lean_Declaration_foldExprM___redArg(v_inst_509_, v_decl_512_, v___f_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_decl_521_, lean_object* v_fn_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Declaration_forEachSorryM___redArg(v_inst_518_, v_inst_519_, v_inst_520_, v_decl_521_, v_fn_522_);
return v___x_523_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
