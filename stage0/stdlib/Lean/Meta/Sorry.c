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
lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___x_85_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v_a_108_; uint8_t v___x_109_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_106_ = 1;
v___x_107_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_85_, v___x_106_, v_a_78_);
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_unbox(v_a_108_);
lean_dec(v_a_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
lean_dec_ref(v_type_73_);
v___x_110_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
v___y_87_ = v_a_75_;
v___y_88_ = v_a_76_;
v___y_89_ = v_a_77_;
v___y_90_ = v_a_78_;
goto v___jp_86_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* v_type_119_, lean_object* v_synthetic_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_synthetic_boxed_126_; lean_object* v_res_127_; 
v_synthetic_boxed_126_ = lean_unbox(v_synthetic_120_);
v_res_127_ = l_Lean_Meta_mkSorry(v_type_119_, v_synthetic_boxed_126_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* v_view_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___y_134_; 
if (lean_obj_tag(v_view_129_) == 1)
{
lean_object* v_val_138_; lean_object* v_range_139_; lean_object* v_pos_140_; lean_object* v_endPos_141_; lean_object* v_module_142_; lean_object* v_charUtf16_143_; lean_object* v_endCharUtf16_144_; lean_object* v_line_145_; lean_object* v_column_146_; lean_object* v_line_147_; lean_object* v_column_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_val_138_ = lean_ctor_get(v_view_129_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_view_129_, 1);
v_range_139_ = lean_ctor_get(v_val_138_, 1);
lean_inc_ref(v_range_139_);
v_pos_140_ = lean_ctor_get(v_range_139_, 0);
lean_inc_ref(v_pos_140_);
v_endPos_141_ = lean_ctor_get(v_range_139_, 2);
lean_inc_ref(v_endPos_141_);
v_module_142_ = lean_ctor_get(v_val_138_, 0);
lean_inc(v_module_142_);
lean_dec(v_val_138_);
v_charUtf16_143_ = lean_ctor_get(v_range_139_, 1);
lean_inc(v_charUtf16_143_);
v_endCharUtf16_144_ = lean_ctor_get(v_range_139_, 3);
lean_inc(v_endCharUtf16_144_);
lean_dec_ref(v_range_139_);
v_line_145_ = lean_ctor_get(v_pos_140_, 0);
lean_inc(v_line_145_);
v_column_146_ = lean_ctor_get(v_pos_140_, 1);
lean_inc(v_column_146_);
lean_dec_ref(v_pos_140_);
v_line_147_ = lean_ctor_get(v_endPos_141_, 0);
lean_inc(v_line_147_);
v_column_148_ = lean_ctor_get(v_endPos_141_, 1);
lean_inc(v_column_148_);
lean_dec_ref(v_endPos_141_);
v___x_149_ = l_Lean_Name_num___override(v_module_142_, v_line_145_);
v___x_150_ = l_Lean_Name_num___override(v___x_149_, v_column_146_);
v___x_151_ = l_Lean_Name_num___override(v___x_150_, v_line_147_);
v___x_152_ = l_Lean_Name_num___override(v___x_151_, v_column_148_);
v___x_153_ = l_Lean_Name_num___override(v___x_152_, v_charUtf16_143_);
v___x_154_ = l_Lean_Name_num___override(v___x_153_, v_endCharUtf16_144_);
v___y_134_ = v___x_154_;
goto v___jp_133_;
}
else
{
lean_object* v___x_155_; 
lean_dec(v_view_129_);
v___x_155_ = lean_box(0);
v___y_134_ = v___x_155_;
goto v___jp_133_;
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_136_ = l_Lean_Name_str___override(v___y_134_, v___x_135_);
v___x_137_ = l_Lean_Core_mkFreshUserName(v___x_136_, v_a_130_, v_a_131_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object* v_view_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_SorryLabelView_encode(v_view_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object* v_name_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Lean_Name_hasMacroScopes(v_name_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Name_eraseMacroScopes(v_name_161_);
if (lean_obj_tag(v___x_164_) == 1)
{
lean_object* v_pre_165_; lean_object* v_str_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_pre_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_pre_165_);
v_str_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc_ref(v_str_166_);
lean_dec_ref_known(v___x_164_, 2);
v___x_167_ = ((lean_object*)(l_Lean_Meta_SorryLabelView_encode___closed__0));
v___x_168_ = lean_string_dec_eq(v_str_166_, v___x_167_);
lean_dec_ref(v_str_166_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v_pre_165_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
if (lean_obj_tag(v_pre_165_) == 2)
{
lean_object* v_pre_170_; 
v_pre_170_ = lean_ctor_get(v_pre_165_, 0);
lean_inc(v_pre_170_);
if (lean_obj_tag(v_pre_170_) == 2)
{
lean_object* v_pre_171_; 
v_pre_171_ = lean_ctor_get(v_pre_170_, 0);
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
lean_object* v_i_175_; lean_object* v_i_176_; lean_object* v_i_177_; lean_object* v_i_178_; lean_object* v_i_179_; lean_object* v_pre_180_; lean_object* v_i_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_i_175_ = lean_ctor_get(v_pre_165_, 1);
lean_inc(v_i_175_);
lean_dec_ref_known(v_pre_165_, 2);
v_i_176_ = lean_ctor_get(v_pre_170_, 1);
lean_inc(v_i_176_);
lean_dec_ref_known(v_pre_170_, 2);
v_i_177_ = lean_ctor_get(v_pre_171_, 1);
lean_inc(v_i_177_);
lean_dec_ref_known(v_pre_171_, 2);
v_i_178_ = lean_ctor_get(v_pre_172_, 1);
lean_inc(v_i_178_);
lean_dec_ref_known(v_pre_172_, 2);
v_i_179_ = lean_ctor_get(v_pre_173_, 1);
lean_inc(v_i_179_);
lean_dec_ref_known(v_pre_173_, 2);
v_pre_180_ = lean_ctor_get(v_pre_174_, 0);
lean_inc(v_pre_180_);
v_i_181_ = lean_ctor_get(v_pre_174_, 1);
lean_inc(v_i_181_);
lean_dec_ref_known(v_pre_174_, 2);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_i_181_);
lean_ctor_set(v___x_182_, 1, v_i_179_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_i_178_);
lean_ctor_set(v___x_183_, 1, v_i_177_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v_i_176_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
lean_ctor_set(v___x_184_, 3, v_i_175_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_pre_180_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; 
lean_dec(v_pre_174_);
lean_dec_ref_known(v_pre_173_, 2);
lean_dec_ref_known(v_pre_172_, 2);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_170_, 2);
lean_dec_ref_known(v_pre_165_, 2);
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
else
{
lean_object* v___x_189_; 
lean_dec(v_pre_173_);
lean_dec_ref_known(v_pre_172_, 2);
lean_dec_ref_known(v_pre_171_, 2);
lean_dec_ref_known(v_pre_170_, 2);
lean_dec_ref_known(v_pre_165_, 2);
v___x_189_ = lean_box(0);
return v___x_189_;
}
}
else
{
lean_object* v___x_190_; 
lean_dec_ref_known(v_pre_171_, 2);
lean_dec(v_pre_172_);
lean_dec_ref_known(v_pre_170_, 2);
lean_dec_ref_known(v_pre_165_, 2);
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v_pre_171_);
lean_dec_ref_known(v_pre_170_, 2);
lean_dec_ref_known(v_pre_165_, 2);
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
else
{
lean_object* v___x_192_; 
lean_dec_ref_known(v_pre_165_, 2);
lean_dec(v_pre_170_);
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec(v_pre_165_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v___x_164_);
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f___boxed(lean_object* v_name_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_name_195_);
lean_dec(v_name_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v___x_201_; lean_object* v_mainModule_202_; lean_object* v___x_203_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v___x_201_ = l_Lean_Environment_header(v_env_200_);
lean_dec_ref(v_env_200_);
v_mainModule_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_mainModule_202_);
lean_dec_ref(v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_mainModule_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_204_);
lean_dec(v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_218_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__7(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__6));
v___x_232_ = l_Lean_mkConst(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__11(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Lean_Level_succ___override(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__12(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__13(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__12, &l_Lean_Meta_mkLabeledSorry___closed__12_once, _init_l_Lean_Meta_mkLabeledSorry___closed__12);
v___x_244_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__11, &l_Lean_Meta_mkLabeledSorry___closed__11_once, _init_l_Lean_Meta_mkLabeledSorry___closed__11);
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__14(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__13, &l_Lean_Meta_mkLabeledSorry___closed__13_once, _init_l_Lean_Meta_mkLabeledSorry___closed__13);
v___x_247_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_248_ = l_Lean_mkConst(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__15(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_box(0);
v___x_250_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_251_ = l_Lean_mkConst(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__18(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_258_ = l_Lean_mkConst(v___x_257_, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* v_type_259_, uint8_t v_synthetic_260_, uint8_t v_unique_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_tag_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v_a_372_; uint8_t v___x_373_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__2));
v___x_370_ = 1;
v___x_371_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(v___x_267_, v___x_370_, v_a_265_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v___x_373_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_type_259_);
v___x_374_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
v___y_325_ = v_a_262_;
v___y_326_ = v_a_263_;
v___y_327_ = v_a_264_;
v___y_328_ = v_a_265_;
goto v___jp_324_;
}
v___jp_268_:
{
if (v_unique_261_ == 0)
{
lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_275_ = 0;
v___x_276_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__7, &l_Lean_Meta_mkLabeledSorry___closed__7_once, _init_l_Lean_Meta_mkLabeledSorry___closed__7);
v___x_277_ = l_Lean_mkForall(v___x_274_, v___x_275_, v___x_276_, v_type_259_);
v___x_278_ = l_Lean_Meta_mkSorry(v___x_277_, v_synthetic_260_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_292_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_292_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__14, &l_Lean_Meta_mkLabeledSorry___closed__14_once, _init_l_Lean_Meta_mkLabeledSorry___closed__14);
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_285_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__18, &l_Lean_Meta_mkLabeledSorry___closed__18_once, _init_l_Lean_Meta_mkLabeledSorry___closed__18);
v___x_286_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_269_);
v___x_287_ = l_Lean_mkApp4(v___x_283_, v___x_276_, v___x_284_, v___x_285_, v___x_286_);
v___x_288_ = l_Lean_Expr_app___override(v_a_279_, v___x_287_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_288_);
v___x_290_ = v___x_281_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_dec(v_tag_269_);
return v___x_278_;
}
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__4));
v___x_294_ = 0;
v___x_295_ = lean_obj_once(&l_Lean_Meta_mkLabeledSorry___closed__15, &l_Lean_Meta_mkLabeledSorry___closed__15_once, _init_l_Lean_Meta_mkLabeledSorry___closed__15);
v___x_296_ = l_Lean_mkForall(v___x_293_, v___x_294_, v___x_295_, v_type_259_);
v___x_297_ = l_Lean_Meta_mkSorry(v___x_296_, v_synthetic_260_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_307_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_307_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_269_);
v___x_303_ = l_Lean_Expr_app___override(v_a_298_, v___x_302_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_303_);
v___x_305_ = v___x_300_;
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
else
{
lean_dec(v_tag_269_);
return v___x_297_;
}
}
}
v___jp_308_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_box(0);
v___x_314_ = l_Lean_Meta_SorryLabelView_encode(v___x_313_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v_tag_269_ = v_a_315_;
v___y_270_ = v___y_309_;
v___y_271_ = v___y_310_;
v___y_272_ = v___y_311_;
v___y_273_ = v___y_312_;
goto v___jp_268_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_type_259_);
v_a_316_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
v___jp_324_:
{
lean_object* v_fileMap_329_; lean_object* v_ref_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v_fileMap_329_ = lean_ctor_get(v___y_327_, 1);
v_ref_330_ = lean_ctor_get(v___y_327_, 5);
v___x_331_ = 0;
v___x_332_ = l_Lean_Syntax_getPos_x3f(v_ref_330_, v___x_331_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = l_Lean_Syntax_getTailPos_x3f(v_ref_330_, v___x_331_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_369_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_369_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_369_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_369_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_character_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_character_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_367_; 
v___x_339_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_328_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
lean_inc_ref_n(v_fileMap_329_, 4);
v___x_341_ = l_Lean_FileMap_toPosition(v_fileMap_329_, v_val_333_);
v___x_342_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_329_, v_val_333_);
lean_dec(v_val_333_);
v_character_343_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_character_343_);
lean_dec_ref(v___x_342_);
v___x_344_ = l_Lean_FileMap_toPosition(v_fileMap_329_, v_val_335_);
v___x_345_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_329_, v_val_335_);
lean_dec(v_val_335_);
v_character_346_ = lean_ctor_get(v___x_345_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v___x_345_, 0);
lean_dec(v_unused_368_);
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_367_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_character_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_367_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_341_);
lean_ctor_set(v___x_350_, 1, v_character_343_);
lean_ctor_set(v___x_350_, 2, v___x_344_);
lean_ctor_set(v___x_350_, 3, v_character_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_350_);
lean_ctor_set(v___x_348_, 0, v_a_340_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_340_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_366_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_352_);
v___x_354_ = v___x_337_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_365_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_SorryLabelView_encode(v___x_354_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v_tag_269_ = v_a_356_;
v___y_270_ = v___y_325_;
v___y_271_ = v___y_326_;
v___y_272_ = v___y_327_;
v___y_273_ = v___y_328_;
goto v___jp_268_;
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_type_259_);
v_a_357_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_355_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
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
lean_dec(v___x_334_);
lean_dec(v_val_333_);
v___y_309_ = v___y_325_;
v___y_310_ = v___y_326_;
v___y_311_ = v___y_327_;
v___y_312_ = v___y_328_;
goto v___jp_308_;
}
}
else
{
lean_dec(v___x_332_);
v___y_309_ = v___y_325_;
v___y_310_ = v___y_326_;
v___y_311_ = v___y_327_;
v___y_312_ = v___y_328_;
goto v___jp_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* v_type_383_, lean_object* v_synthetic_384_, lean_object* v_unique_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
uint8_t v_synthetic_boxed_391_; uint8_t v_unique_boxed_392_; lean_object* v_res_393_; 
v_synthetic_boxed_391_ = lean_unbox(v_synthetic_384_);
v_unique_boxed_392_ = lean_unbox(v_unique_385_);
v_res_393_ = l_Lean_Meta_mkLabeledSorry(v_type_383_, v_synthetic_boxed_391_, v_unique_boxed_392_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object* v_e_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Meta_mkSorry___closed__1));
v___x_396_ = l_Lean_Expr_isAppOf(v_e_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_box(0);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = l_Lean_Expr_getAppNumArgs(v_e_394_);
v___x_399_ = lean_unsigned_to_nat(3u);
v___x_400_ = lean_nat_dec_le(v___x_399_, v___x_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = lean_unsigned_to_nat(2u);
v___x_403_ = lean_nat_sub(v___x_398_, v___x_402_);
lean_dec(v___x_398_);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_sub(v___x_403_, v___x_404_);
lean_dec(v___x_403_);
v___x_406_ = l_Lean_Expr_getRevArg_x21(v_e_394_, v___x_405_);
lean_inc_ref(v___x_406_);
v___x_407_ = l_Lean_Expr_name_x3f(v___x_406_);
if (lean_obj_tag(v___x_407_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_406_);
v_val_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_408_);
lean_dec(v_val_408_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
lean_dec(v___x_407_);
v___x_410_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__10));
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = l_Lean_Expr_isAppOfArity(v___x_406_, v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref(v___x_406_);
v___x_413_ = lean_box(0);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_414_ = l_Lean_Expr_appFn_x21(v___x_406_);
v___x_415_ = l_Lean_Expr_appArg_x21(v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_Meta_mkLabeledSorry___closed__17));
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_Expr_isAppOfArity(v___x_415_, v___x_416_, v___x_417_);
lean_dec_ref(v___x_415_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec_ref(v___x_406_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = l_Lean_Expr_appArg_x21(v___x_406_);
lean_dec_ref(v___x_406_);
v___x_421_ = l_Lean_Expr_name_x3f(v___x_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
else
{
lean_object* v_val_423_; lean_object* v___x_424_; 
v_val_423_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v___x_421_, 1);
v___x_424_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_423_);
lean_dec(v_val_423_);
return v___x_424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object* v_e_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_425_);
lean_dec_ref(v_e_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object* v_e_427_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_Expr_isSorry(v_e_427_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_427_);
if (lean_obj_tag(v___x_436_) == 0)
{
goto v___jp_428_;
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_447_; 
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_436_, 0);
lean_dec(v_unused_448_);
v___x_438_ = v___x_436_;
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
else
{
lean_dec(v___x_436_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
if (v___x_434_ == 0)
{
lean_del_object(v___x_438_);
goto v___jp_428_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_440_ = l_Lean_Expr_getAppNumArgs(v_e_427_);
v___x_441_ = lean_unsigned_to_nat(3u);
v___x_442_ = lean_nat_sub(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
v___x_443_ = l_Lean_Expr_getBoundedAppFn(v___x_442_, v_e_427_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_443_);
v___x_445_ = v___x_438_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_429_ = l_Lean_Expr_getAppNumArgs(v_e_427_);
v___x_430_ = lean_unsigned_to_nat(2u);
v___x_431_ = lean_nat_sub(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___x_432_ = l_Lean_Expr_getBoundedAppFn(v___x_431_, v_e_427_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object* v_e_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Expr_getSorry_x3f(v_e_449_);
lean_dec_ref(v_e_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object* v_toPure_451_, lean_object* v_____r_452_){
_start:
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 0;
v___x_454_ = lean_box(v___x_453_);
v___x_455_ = lean_apply_2(v_toPure_451_, lean_box(0), v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object* v_fn_456_, lean_object* v_toBind_457_, lean_object* v___f_458_, lean_object* v_toPure_459_, lean_object* v_e_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Expr_getSorry_x3f(v_e_460_);
if (lean_obj_tag(v___x_461_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_toPure_459_);
v_val_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_apply_1(v_fn_456_, v_val_462_);
v___x_464_ = lean_apply_4(v_toBind_457_, lean_box(0), lean_box(0), v___x_463_, v___f_458_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v___x_461_);
lean_dec(v___f_458_);
lean_dec(v_toBind_457_);
lean_dec(v_fn_456_);
v___x_465_ = 1;
v___x_466_ = lean_box(v___x_465_);
v___x_467_ = lean_apply_2(v_toPure_459_, lean_box(0), v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object* v_fn_468_, lean_object* v_toBind_469_, lean_object* v___f_470_, lean_object* v_toPure_471_, lean_object* v_e_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_forEachSorryM___redArg___lam__1(v_fn_468_, v_toBind_469_, v___f_470_, v_toPure_471_, v_e_472_);
lean_dec_ref(v_e_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_input_477_, lean_object* v_fn_478_){
_start:
{
lean_object* v_toApplicative_479_; lean_object* v_toBind_480_; lean_object* v_toPure_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v_toApplicative_479_ = lean_ctor_get(v_inst_474_, 0);
v_toBind_480_ = lean_ctor_get(v_inst_474_, 1);
v_toPure_481_ = lean_ctor_get(v_toApplicative_479_, 1);
lean_inc_n(v_toPure_481_, 2);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_482_, 0, v_toPure_481_);
lean_inc(v_toBind_480_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_483_, 0, v_fn_478_);
lean_closure_set(v___f_483_, 1, v_toBind_480_);
lean_closure_set(v___f_483_, 2, v___f_482_);
lean_closure_set(v___f_483_, 3, v_toPure_481_);
v___x_484_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_474_, v_inst_475_, v_inst_476_, v_input_477_, v___f_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object* v_m_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_input_489_, lean_object* v_fn_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_486_, v_inst_487_, v_inst_488_, v_input_489_, v_fn_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_fn_495_, lean_object* v_x_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_forEachSorryM___redArg(v_inst_492_, v_inst_493_, v_inst_494_, v_a_497_, v_fn_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_decl_502_, lean_object* v_fn_503_){
_start:
{
lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc_ref(v_inst_499_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Declaration_forEachSorryM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_504_, 0, v_inst_499_);
lean_closure_set(v___f_504_, 1, v_inst_500_);
lean_closure_set(v___f_504_, 2, v_inst_501_);
lean_closure_set(v___f_504_, 3, v_fn_503_);
v___x_505_ = lean_box(0);
v___x_506_ = l_Lean_Declaration_foldExprM___redArg(v_inst_499_, v_decl_502_, v___f_504_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_decl_511_, lean_object* v_fn_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Declaration_forEachSorryM___redArg(v_inst_508_, v_inst_509_, v_inst_510_, v_decl_511_, v_fn_512_);
return v___x_513_;
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
