// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Entails
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Util public import Lean.Meta.Sym.Util
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
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Expected SPred.entails: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Applying "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "of_entails_wp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 31, 210, 183, 145, 91, 10, 79)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Not a SPred.entails: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Not a forall: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PostCond"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 111, 255, 27, 103, 9, 244, 9)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " failed. It should not."};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "after applying "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "entails_cons_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 192, 217, 126, 138, 217, 120, 234)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Failed to introduce state at "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " despite "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " spec potential"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "pure_elim'"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 100, 201, 175, 219, 207, 33, 227)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(83, 183, 133, 62, 214, 202, 136, 98)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "entails_nil_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(209, 42, 38, 114, 220, 245, 181, 209)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "pure_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 52, 84, 252, 44, 75, 13, 225)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_x_30_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_29_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_53_, v_x_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(lean_object* v_00_u03b1_68_, lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___boxed(lean_object* v_00_u03b1_84_, lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(v_00_u03b1_84_, v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v___x_108_; lean_object* v_mctx_109_; lean_object* v_lctx_110_; lean_object* v_options_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = lean_st_ref_get(v___y_102_);
v_mctx_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_mctx_109_);
lean_dec(v___x_108_);
v_lctx_110_ = lean_ctor_get(v___y_101_, 2);
v_options_111_ = lean_ctor_get(v___y_103_, 2);
lean_inc_ref(v_options_111_);
lean_inc_ref(v_lctx_110_);
v___x_112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_112_, 0, v_env_107_);
lean_ctor_set(v___x_112_, 1, v_mctx_109_);
lean_ctor_set(v___x_112_, 2, v_lctx_110_);
lean_ctor_set(v___x_112_, 3, v_options_111_);
v___x_113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_msgData_100_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0___boxed(lean_object* v_msgData_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msgData_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(lean_object* v_msg_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_ref_128_; lean_object* v___x_129_; lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_ref_128_ = lean_ctor_get(v___y_125_, 5);
v___x_129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msg_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_inc(v_ref_128_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_ref_128_);
lean_ctor_set(v___x_134_, 1, v_a_130_);
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 1);
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg___boxed(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(lean_object* v_f_146_, lean_object* v_a_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___y_156_; lean_object* v___x_159_; uint8_t v_debug_160_; 
v___x_159_ = lean_st_ref_get(v___y_149_);
v_debug_160_ = lean_ctor_get_uint8(v___x_159_, sizeof(void*)*10);
lean_dec(v___x_159_);
if (v_debug_160_ == 0)
{
v___y_156_ = v___y_149_;
goto v___jp_155_;
}
else
{
lean_object* v___x_161_; 
lean_inc_ref(v_f_146_);
v___x_161_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_146_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; 
lean_dec_ref_known(v___x_161_, 1);
lean_inc_ref(v_a_147_);
v___x_162_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_dec_ref_known(v___x_162_, 1);
v___y_156_ = v___y_149_;
goto v___jp_155_;
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec_ref(v_a_147_);
lean_dec_ref(v_f_146_);
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v_a_147_);
lean_dec_ref(v_f_146_);
v_a_171_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_161_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_161_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = l_Lean_Expr_app___override(v_f_146_, v_a_147_);
v___x_158_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_157_, v___y_156_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg___boxed(lean_object* v_f_179_, lean_object* v_a_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_179_, v_a_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(lean_object* v_f_189_, lean_object* v_a_u2081_190_, lean_object* v_a_u2082_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_189_, v_a_u2081_190_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v___x_206_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_205_, v_a_u2082_191_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
return v___x_206_;
}
else
{
lean_dec_ref(v_a_u2082_191_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2___boxed(lean_object* v_f_207_, lean_object* v_a_u2081_208_, lean_object* v_a_u2082_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_207_, v_a_u2081_208_, v_a_u2082_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(lean_object* v_f_223_, lean_object* v_a_u2081_224_, lean_object* v_a_u2082_225_, lean_object* v_a_u2083_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_223_, v_a_u2081_224_, v_a_u2082_225_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_240_, v_a_u2083_226_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
return v___x_241_;
}
else
{
lean_dec_ref(v_a_u2083_226_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1___boxed(lean_object* v_f_242_, lean_object* v_a_u2081_243_, lean_object* v_a_u2082_244_, lean_object* v_a_u2083_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v_f_242_, v_a_u2081_243_, v_a_u2082_244_, v_a_u2083_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(lean_object* v_head_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
lean_inc(v_head_271_);
v___x_284_ = l_Lean_MVarId_getType(v_head_271_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_n(v_a_285_, 2);
lean_dec_ref_known(v___x_284_, 1);
v___x_302_ = l_Lean_Expr_cleanupAnnotations(v_a_285_);
v___x_303_ = l_Lean_Expr_isApp(v___x_302_);
if (v___x_303_ == 0)
{
lean_dec_ref(v___x_302_);
lean_dec(v_head_271_);
v___y_287_ = v___y_272_;
v___y_288_ = v___y_273_;
v___y_289_ = v___y_274_;
v___y_290_ = v___y_275_;
v___y_291_ = v___y_276_;
v___y_292_ = v___y_277_;
v___y_293_ = v___y_278_;
v___y_294_ = v___y_279_;
v___y_295_ = v___y_280_;
v___y_296_ = v___y_281_;
v___y_297_ = v___y_282_;
goto v___jp_286_;
}
else
{
lean_object* v_arg_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_arg_304_ = lean_ctor_get(v___x_302_, 1);
lean_inc_ref(v_arg_304_);
v___x_305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_302_);
v___x_306_ = l_Lean_Expr_isApp(v___x_305_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v_arg_304_);
lean_dec(v_head_271_);
v___y_287_ = v___y_272_;
v___y_288_ = v___y_273_;
v___y_289_ = v___y_274_;
v___y_290_ = v___y_275_;
v___y_291_ = v___y_276_;
v___y_292_ = v___y_277_;
v___y_293_ = v___y_278_;
v___y_294_ = v___y_279_;
v___y_295_ = v___y_280_;
v___y_296_ = v___y_281_;
v___y_297_ = v___y_282_;
goto v___jp_286_;
}
else
{
lean_object* v_arg_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_arg_307_ = lean_ctor_get(v___x_305_, 1);
lean_inc_ref(v_arg_307_);
v___x_308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_305_);
v___x_309_ = l_Lean_Expr_isApp(v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v___x_308_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_304_);
lean_dec(v_head_271_);
v___y_287_ = v___y_272_;
v___y_288_ = v___y_273_;
v___y_289_ = v___y_274_;
v___y_290_ = v___y_275_;
v___y_291_ = v___y_276_;
v___y_292_ = v___y_277_;
v___y_293_ = v___y_278_;
v___y_294_ = v___y_279_;
v___y_295_ = v___y_280_;
v___y_296_ = v___y_281_;
v___y_297_ = v___y_282_;
goto v___jp_286_;
}
else
{
lean_object* v_arg_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_arg_310_ = lean_ctor_get(v___x_308_, 1);
lean_inc_ref(v_arg_310_);
v___x_311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_308_);
v___x_312_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_311_);
lean_dec_ref(v_arg_310_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_304_);
lean_dec(v_head_271_);
v___y_287_ = v___y_272_;
v___y_288_ = v___y_273_;
v___y_289_ = v___y_274_;
v___y_290_ = v___y_275_;
v___y_291_ = v___y_276_;
v___y_292_ = v___y_277_;
v___y_293_ = v___y_278_;
v___y_294_ = v___y_279_;
v___y_295_ = v___y_280_;
v___y_296_ = v___y_281_;
v___y_297_ = v___y_282_;
goto v___jp_286_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_a_285_);
v___x_314_ = l_Lean_Meta_Sym_unfoldReducible(v_arg_310_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_315_, v___y_278_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_311_, v_a_317_, v_arg_307_, v_arg_304_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = l_Lean_MVarId_replaceTargetDefEq(v_head_271_, v_a_319_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_head_271_);
v_a_321_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_318_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v___x_311_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_304_);
lean_dec(v_head_271_);
v_a_329_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_316_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_316_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v___x_311_);
lean_dec_ref(v_arg_307_);
lean_dec_ref(v_arg_304_);
lean_dec(v_head_271_);
v_a_337_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_314_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_314_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
v___jp_286_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1);
v___x_299_ = l_Lean_MessageData_ofExpr(v_a_285_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_300_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_301_;
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_head_271_);
v_a_345_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_284_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_284_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed(lean_object* v_head_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(v_head_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5(void){
_start:
{
uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = 0;
v___x_378_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4));
v___x_379_ = l_Lean_MessageData_ofConstName(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5);
v___x_381_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8);
v___x_387_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(lean_object* v_goal_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_tripleOfEntailsWPRule_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_tripleOfEntailsWPRule_405_ = lean_ctor_get(v___y_393_, 14);
v___x_406_ = lean_box(0);
lean_inc(v_goal_392_);
lean_inc_ref(v_tripleOfEntailsWPRule_405_);
v___x_407_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_tripleOfEntailsWPRule_405_, v_goal_392_, v___x_406_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_mvarIds_427_; 
v_mvarIds_427_ = lean_ctor_get(v_a_408_, 0);
lean_inc(v_mvarIds_427_);
lean_dec_ref_known(v_a_408_, 1);
if (lean_obj_tag(v_mvarIds_427_) == 1)
{
lean_object* v_tail_428_; 
v_tail_428_ = lean_ctor_get(v_mvarIds_427_, 1);
if (lean_obj_tag(v_tail_428_) == 0)
{
lean_object* v_head_429_; lean_object* v___f_430_; lean_object* v___x_431_; 
lean_dec(v_goal_392_);
v_head_429_ = lean_ctor_get(v_mvarIds_427_, 0);
lean_inc_n(v_head_429_, 2);
lean_dec_ref_known(v_mvarIds_427_, 2);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed), 13, 1);
lean_closure_set(v___f_430_, 0, v_head_429_);
v___x_431_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_429_, v___f_430_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_431_;
}
else
{
lean_dec_ref_known(v_mvarIds_427_, 2);
v___y_410_ = v___y_393_;
v___y_411_ = v___y_394_;
v___y_412_ = v___y_395_;
v___y_413_ = v___y_396_;
v___y_414_ = v___y_397_;
v___y_415_ = v___y_398_;
v___y_416_ = v___y_399_;
v___y_417_ = v___y_400_;
v___y_418_ = v___y_401_;
v___y_419_ = v___y_402_;
v___y_420_ = v___y_403_;
goto v___jp_409_;
}
}
else
{
lean_dec(v_mvarIds_427_);
v___y_410_ = v___y_393_;
v___y_411_ = v___y_394_;
v___y_412_ = v___y_395_;
v___y_413_ = v___y_396_;
v___y_414_ = v___y_397_;
v___y_415_ = v___y_398_;
v___y_416_ = v___y_399_;
v___y_417_ = v___y_400_;
v___y_418_ = v___y_401_;
v___y_419_ = v___y_402_;
v___y_420_ = v___y_403_;
goto v___jp_409_;
}
}
else
{
lean_dec(v_a_408_);
v___y_410_ = v___y_393_;
v___y_411_ = v___y_394_;
v___y_412_ = v___y_395_;
v___y_413_ = v___y_396_;
v___y_414_ = v___y_397_;
v___y_415_ = v___y_398_;
v___y_416_ = v___y_399_;
v___y_417_ = v___y_400_;
v___y_418_ = v___y_401_;
v___y_419_ = v___y_402_;
v___y_420_ = v___y_403_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_421_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_goal_392_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_425_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_426_;
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_goal_392_);
v_a_432_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_407_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_407_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed(lean_object* v_goal_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(v_goal_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(lean_object* v_goal_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
lean_inc(v_goal_454_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed), 13, 1);
lean_closure_set(v___f_467_, 0, v_goal_454_);
v___x_468_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_454_, v___f_467_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___boxed(lean_object* v_goal_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(v_goal_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(lean_object* v_00_u03b1_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v_msg_484_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___boxed(lean_object* v_00_u03b1_498_, lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(v_00_u03b1_498_, v_msg_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(lean_object* v_f_513_, lean_object* v_a_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_513_, v_a_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___boxed(lean_object* v_f_528_, lean_object* v_a_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(v_f_528_, v_a_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(lean_object* v_00___543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed(lean_object* v_00___558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(v_00___558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(lean_object* v_goal_578_, lean_object* v___f_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
lean_inc(v_goal_578_);
v___x_592_ = l_Lean_MVarId_getType(v_goal_578_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_762_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_762_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_762_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_762_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = l_Lean_Expr_cleanupAnnotations(v_a_593_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v___x_602_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
goto v___jp_597_;
}
else
{
lean_object* v_arg_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_arg_604_ = lean_ctor_get(v___x_602_, 1);
lean_inc_ref(v_arg_604_);
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_606_ = l_Lean_Expr_isApp(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec_ref(v___x_605_);
lean_dec_ref(v_arg_604_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
goto v___jp_597_;
}
else
{
lean_object* v_arg_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_arg_607_ = lean_ctor_get(v___x_605_, 1);
lean_inc_ref(v_arg_607_);
v___x_608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_605_);
v___x_609_ = l_Lean_Expr_isApp(v___x_608_);
if (v___x_609_ == 0)
{
lean_dec_ref(v___x_608_);
lean_dec_ref(v_arg_607_);
lean_dec_ref(v_arg_604_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
goto v___jp_597_;
}
else
{
lean_object* v_arg_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_arg_610_ = lean_ctor_get(v___x_608_, 1);
lean_inc_ref(v_arg_610_);
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_608_);
v___x_612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1));
v___x_613_ = l_Lean_Expr_isConstOf(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v_arg_607_);
lean_dec_ref(v_arg_604_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
goto v___jp_597_;
}
else
{
lean_object* v___x_614_; 
lean_del_object(v___x_595_);
v___x_614_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_arg_607_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_arg_604_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_611_, v_arg_610_, v_a_615_, v_a_617_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_578_, v_a_619_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_729_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_729_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_729_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_729_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_exceptCondsEntailsRflRule_630_; lean_object* v_exceptCondsEntailsPureRule_631_; lean_object* v_exceptCondsEntailsFalseRule_632_; lean_object* v_exceptCondsEntailsTrueRule_633_; lean_object* v___x_634_; lean_object* v___y_636_; lean_object* v_exceptCondsEntailsRflRule_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_662_; lean_object* v_exceptCondsEntailsRflRule_663_; lean_object* v_exceptCondsEntailsTrueRule_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___x_688_; 
v_exceptCondsEntailsRflRule_630_ = lean_ctor_get(v___y_580_, 10);
v_exceptCondsEntailsPureRule_631_ = lean_ctor_get(v___y_580_, 11);
v_exceptCondsEntailsFalseRule_632_ = lean_ctor_get(v___y_580_, 12);
v_exceptCondsEntailsTrueRule_633_ = lean_ctor_get(v___y_580_, 13);
v___x_634_ = lean_box(0);
lean_inc(v_a_621_);
lean_inc_ref(v_exceptCondsEntailsPureRule_631_);
v___x_688_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_exceptCondsEntailsPureRule_631_, v_a_621_, v___x_634_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___y_691_; lean_object* v_exceptCondsEntailsRflRule_692_; lean_object* v_exceptCondsEntailsFalseRule_693_; lean_object* v_exceptCondsEntailsTrueRule_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v_a_689_) == 1)
{
lean_object* v_mvarIds_718_; 
v_mvarIds_718_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_mvarIds_718_);
lean_dec_ref_known(v_a_689_, 1);
if (lean_obj_tag(v_mvarIds_718_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
v___x_719_ = lean_box(0);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_720_ = lean_apply_13(v___f_579_, v___x_719_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, lean_box(0));
return v___x_720_;
}
else
{
lean_dec(v_mvarIds_718_);
v___y_691_ = v___y_580_;
v_exceptCondsEntailsRflRule_692_ = v_exceptCondsEntailsRflRule_630_;
v_exceptCondsEntailsFalseRule_693_ = v_exceptCondsEntailsFalseRule_632_;
v_exceptCondsEntailsTrueRule_694_ = v_exceptCondsEntailsTrueRule_633_;
v___y_695_ = v___y_581_;
v___y_696_ = v___y_582_;
v___y_697_ = v___y_583_;
v___y_698_ = v___y_584_;
v___y_699_ = v___y_585_;
v___y_700_ = v___y_586_;
v___y_701_ = v___y_587_;
v___y_702_ = v___y_588_;
v___y_703_ = v___y_589_;
v___y_704_ = v___y_590_;
goto v___jp_690_;
}
}
else
{
lean_dec(v_a_689_);
v___y_691_ = v___y_580_;
v_exceptCondsEntailsRflRule_692_ = v_exceptCondsEntailsRflRule_630_;
v_exceptCondsEntailsFalseRule_693_ = v_exceptCondsEntailsFalseRule_632_;
v_exceptCondsEntailsTrueRule_694_ = v_exceptCondsEntailsTrueRule_633_;
v___y_695_ = v___y_581_;
v___y_696_ = v___y_582_;
v___y_697_ = v___y_583_;
v___y_698_ = v___y_584_;
v___y_699_ = v___y_585_;
v___y_700_ = v___y_586_;
v___y_701_ = v___y_587_;
v___y_702_ = v___y_588_;
v___y_703_ = v___y_589_;
v___y_704_ = v___y_590_;
goto v___jp_690_;
}
v___jp_690_:
{
lean_object* v___x_705_; 
lean_inc(v_a_621_);
lean_inc_ref(v_exceptCondsEntailsFalseRule_693_);
v___x_705_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_exceptCondsEntailsFalseRule_693_, v_a_621_, v___x_634_, v___y_691_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
if (lean_obj_tag(v_a_706_) == 1)
{
lean_object* v_mvarIds_707_; 
v_mvarIds_707_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_mvarIds_707_);
lean_dec_ref_known(v_a_706_, 1);
if (lean_obj_tag(v_mvarIds_707_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
v___x_708_ = lean_box(0);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_691_);
v___x_709_ = lean_apply_13(v___f_579_, v___x_708_, v___y_691_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
return v___x_709_;
}
else
{
lean_dec(v_mvarIds_707_);
v___y_662_ = v___y_691_;
v_exceptCondsEntailsRflRule_663_ = v_exceptCondsEntailsRflRule_692_;
v_exceptCondsEntailsTrueRule_664_ = v_exceptCondsEntailsTrueRule_694_;
v___y_665_ = v___y_695_;
v___y_666_ = v___y_696_;
v___y_667_ = v___y_697_;
v___y_668_ = v___y_698_;
v___y_669_ = v___y_699_;
v___y_670_ = v___y_700_;
v___y_671_ = v___y_701_;
v___y_672_ = v___y_702_;
v___y_673_ = v___y_703_;
v___y_674_ = v___y_704_;
goto v___jp_661_;
}
}
else
{
lean_dec(v_a_706_);
v___y_662_ = v___y_691_;
v_exceptCondsEntailsRflRule_663_ = v_exceptCondsEntailsRflRule_692_;
v_exceptCondsEntailsTrueRule_664_ = v_exceptCondsEntailsTrueRule_694_;
v___y_665_ = v___y_695_;
v___y_666_ = v___y_696_;
v___y_667_ = v___y_697_;
v___y_668_ = v___y_698_;
v___y_669_ = v___y_699_;
v___y_670_ = v___y_700_;
v___y_671_ = v___y_701_;
v___y_672_ = v___y_702_;
v___y_673_ = v___y_703_;
v___y_674_ = v___y_704_;
goto v___jp_661_;
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_579_);
v_a_710_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_705_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_705_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_579_);
v_a_721_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_688_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_688_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
v___jp_625_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
v___jp_635_:
{
lean_object* v___x_648_; 
lean_inc(v_a_621_);
lean_inc_ref(v_exceptCondsEntailsRflRule_637_);
v___x_648_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_exceptCondsEntailsRflRule_637_, v_a_621_, v___x_634_, v___y_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
if (lean_obj_tag(v_a_649_) == 1)
{
lean_object* v_mvarIds_650_; 
v_mvarIds_650_ = lean_ctor_get(v_a_649_, 0);
lean_inc(v_mvarIds_650_);
lean_dec_ref_known(v_a_649_, 1);
if (lean_obj_tag(v_mvarIds_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
v___x_651_ = lean_box(0);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_636_);
v___x_652_ = lean_apply_13(v___f_579_, v___x_651_, v___y_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, lean_box(0));
return v___x_652_;
}
else
{
lean_dec(v_mvarIds_650_);
lean_dec_ref(v___f_579_);
goto v___jp_625_;
}
}
else
{
lean_dec(v_a_649_);
lean_dec_ref(v___f_579_);
goto v___jp_625_;
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_579_);
v_a_653_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_648_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_648_);
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
v___jp_661_:
{
lean_object* v___x_675_; 
lean_inc(v_a_621_);
lean_inc_ref(v_exceptCondsEntailsTrueRule_664_);
v___x_675_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_exceptCondsEntailsTrueRule_664_, v_a_621_, v___x_634_, v___y_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
if (lean_obj_tag(v_a_676_) == 1)
{
lean_object* v_mvarIds_677_; 
v_mvarIds_677_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_mvarIds_677_);
lean_dec_ref_known(v_a_676_, 1);
if (lean_obj_tag(v_mvarIds_677_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
v___x_678_ = lean_box(0);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_662_);
v___x_679_ = lean_apply_13(v___f_579_, v___x_678_, v___y_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, lean_box(0));
return v___x_679_;
}
else
{
lean_dec(v_mvarIds_677_);
v___y_636_ = v___y_662_;
v_exceptCondsEntailsRflRule_637_ = v_exceptCondsEntailsRflRule_663_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_667_;
v___y_641_ = v___y_668_;
v___y_642_ = v___y_669_;
v___y_643_ = v___y_670_;
v___y_644_ = v___y_671_;
v___y_645_ = v___y_672_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_674_;
goto v___jp_635_;
}
}
else
{
lean_dec(v_a_676_);
v___y_636_ = v___y_662_;
v_exceptCondsEntailsRflRule_637_ = v_exceptCondsEntailsRflRule_663_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_667_;
v___y_641_ = v___y_668_;
v___y_642_ = v___y_669_;
v___y_643_ = v___y_670_;
v___y_644_ = v___y_671_;
v___y_645_ = v___y_672_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_674_;
goto v___jp_635_;
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_579_);
v_a_680_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_675_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_675_);
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
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___f_579_);
v_a_730_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_620_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_620_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
v_a_738_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_618_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_618_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_615_);
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
v_a_746_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_616_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_616_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v_arg_604_);
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
v_a_754_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_614_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_614_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
}
v___jp_597_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_box(0);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___f_579_);
lean_dec(v_goal_578_);
v_a_763_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_592_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_592_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed(lean_object* v_goal_771_, lean_object* v___f_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(v_goal_771_, v___f_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(lean_object* v_goal_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; 
v___f_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0));
lean_inc(v_goal_787_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed), 14, 2);
lean_closure_set(v___f_801_, 0, v_goal_787_);
lean_closure_set(v___f_801_, 1, v___f_800_);
v___x_802_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_787_, v___f_801_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed(lean_object* v_goal_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(v_goal_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
return v_res_816_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2));
v___x_822_ = l_Lean_stringToMessageData(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(lean_object* v_head_823_, lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
lean_inc(v_head_823_);
v___x_839_ = l_Lean_MVarId_getType(v_head_823_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
if (lean_obj_tag(v_a_840_) == 7)
{
lean_object* v_binderName_850_; lean_object* v_binderType_851_; lean_object* v_body_852_; uint8_t v_binderInfo_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_binderName_850_ = lean_ctor_get(v_a_840_, 0);
v_binderType_851_ = lean_ctor_get(v_a_840_, 1);
v_body_852_ = lean_ctor_get(v_a_840_, 2);
v_binderInfo_853_ = lean_ctor_get_uint8(v_a_840_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_852_);
v___x_854_ = l_Lean_Expr_cleanupAnnotations(v_body_852_);
v___x_855_ = l_Lean_Expr_isApp(v___x_854_);
if (v___x_855_ == 0)
{
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec(v_head_823_);
v___y_842_ = v___y_834_;
v___y_843_ = v___y_835_;
v___y_844_ = v___y_836_;
v___y_845_ = v___y_837_;
goto v___jp_841_;
}
else
{
lean_object* v_arg_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_arg_856_ = lean_ctor_get(v___x_854_, 1);
lean_inc_ref(v_arg_856_);
v___x_857_ = l_Lean_Expr_appFnCleanup___redArg(v___x_854_);
v___x_858_ = l_Lean_Expr_isApp(v___x_857_);
if (v___x_858_ == 0)
{
lean_dec_ref(v___x_857_);
lean_dec_ref(v_arg_856_);
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec(v_head_823_);
v___y_842_ = v___y_834_;
v___y_843_ = v___y_835_;
v___y_844_ = v___y_836_;
v___y_845_ = v___y_837_;
goto v___jp_841_;
}
else
{
lean_object* v_arg_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_arg_859_ = lean_ctor_get(v___x_857_, 1);
lean_inc_ref(v_arg_859_);
v___x_860_ = l_Lean_Expr_appFnCleanup___redArg(v___x_857_);
v___x_861_ = l_Lean_Expr_isApp(v___x_860_);
if (v___x_861_ == 0)
{
lean_dec_ref(v___x_860_);
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_arg_856_);
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec(v_head_823_);
v___y_842_ = v___y_834_;
v___y_843_ = v___y_835_;
v___y_844_ = v___y_836_;
v___y_845_ = v___y_837_;
goto v___jp_841_;
}
else
{
lean_object* v_arg_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_arg_862_ = lean_ctor_get(v___x_860_, 1);
lean_inc_ref(v_arg_862_);
v___x_863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_860_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4));
v___x_865_ = l_Lean_Name_mkStr4(v___x_824_, v___x_825_, v___x_864_, v___x_826_);
v___x_866_ = l_Lean_Expr_isConstOf(v___x_863_, v___x_865_);
lean_dec(v___x_865_);
if (v___x_866_ == 0)
{
lean_dec_ref(v___x_863_);
lean_dec_ref(v_arg_862_);
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_arg_856_);
lean_dec(v_head_823_);
v___y_842_ = v___y_834_;
v___y_843_ = v___y_835_;
v___y_844_ = v___y_836_;
v___y_845_ = v___y_837_;
goto v___jp_841_;
}
else
{
lean_object* v___x_867_; 
lean_inc_ref(v_binderType_851_);
lean_inc(v_binderName_850_);
lean_dec_ref_known(v_a_840_, 3);
v___x_867_ = l_Lean_Meta_Sym_unfoldReducible(v_arg_862_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_868_, v___y_833_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_863_, v_a_870_, v_arg_859_, v_arg_856_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_Expr_forallE___override(v_binderName_850_, v_binderType_851_, v_a_872_, v_binderInfo_853_);
v___x_874_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_873_, v___y_833_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = l_Lean_MVarId_replaceTargetDefEq(v_head_823_, v_a_875_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_876_;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_head_823_);
v_a_877_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_874_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_binderType_851_);
lean_dec(v_binderName_850_);
lean_dec(v_head_823_);
v_a_885_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_871_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_871_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_863_);
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_arg_856_);
lean_dec_ref(v_binderType_851_);
lean_dec(v_binderName_850_);
lean_dec(v_head_823_);
v_a_893_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_869_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_869_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___x_863_);
lean_dec_ref(v_arg_859_);
lean_dec_ref(v_arg_856_);
lean_dec_ref(v_binderType_851_);
lean_dec(v_binderName_850_);
lean_dec(v_head_823_);
v_a_901_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_867_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_867_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
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
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec(v_head_823_);
v___x_909_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3);
v___x_910_ = l_Lean_MessageData_ofExpr(v_a_840_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_911_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_912_;
}
v___jp_841_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
v___x_847_ = l_Lean_MessageData_ofExpr(v_a_840_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_848_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_849_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec(v_head_823_);
v_a_913_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_839_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_839_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed(lean_object* v_head_921_, lean_object* v___x_922_, lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(v_head_921_, v___x_922_, v___x_923_, v___x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_937_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2(void){
_start:
{
uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = 0;
v___x_945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1));
v___x_946_ = l_Lean_MessageData_ofConstName(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2);
v___x_948_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8);
v___x_951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(lean_object* v_goal_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___x_975_; 
lean_inc(v_goal_956_);
v___x_975_ = l_Lean_MVarId_getType(v_goal_956_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1098_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1098_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1098_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___x_996_; uint8_t v___x_997_; 
lean_inc(v_a_976_);
v___x_996_ = l_Lean_Expr_cleanupAnnotations(v_a_976_);
v___x_997_ = l_Lean_Expr_isApp(v___x_996_);
if (v___x_997_ == 0)
{
lean_dec_ref(v___x_996_);
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
goto v___jp_980_;
}
else
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_996_);
v___x_999_ = l_Lean_Expr_isApp(v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v___x_998_);
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
goto v___jp_980_;
}
else
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_998_);
v___x_1001_ = l_Lean_Expr_isApp(v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v___x_1000_);
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
goto v___jp_980_;
}
else
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1000_);
v___x_1003_ = l_Lean_Expr_isApp(v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v___x_1002_);
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
goto v___jp_980_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1002_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2));
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3));
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5));
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1));
v___x_1009_ = l_Lean_Expr_isConstOf(v___x_1004_, v___x_1008_);
lean_dec_ref(v___x_1004_);
if (v___x_1009_ == 0)
{
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
goto v___jp_980_;
}
else
{
lean_object* v_postCondEntailsRflRule_1010_; lean_object* v_postCondEntailsMkRule_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_978_);
v_postCondEntailsRflRule_1010_ = lean_ctor_get(v___y_957_, 8);
v_postCondEntailsMkRule_1011_ = lean_ctor_get(v___y_957_, 9);
v___x_1012_ = lean_box(0);
lean_inc(v_goal_956_);
lean_inc_ref(v_postCondEntailsRflRule_1010_);
v___x_1013_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_postCondEntailsRflRule_1010_, v_goal_956_, v___x_1012_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1089_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1089_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1089_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___y_1019_; lean_object* v_postCondEntailsMkRule_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; 
if (lean_obj_tag(v_a_1014_) == 1)
{
lean_object* v_mvarIds_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
v_mvarIds_1078_ = lean_ctor_get(v_a_1014_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_1014_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1080_ = v_a_1014_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_mvarIds_1078_);
lean_dec(v_a_1014_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_mvarIds_1078_) == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_mvarIds_1078_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1083_);
v___x_1085_ = v___x_1016_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_del_object(v___x_1080_);
lean_dec(v_mvarIds_1078_);
lean_del_object(v___x_1016_);
v___y_1019_ = v___y_957_;
v_postCondEntailsMkRule_1020_ = v_postCondEntailsMkRule_1011_;
v___y_1021_ = v___y_958_;
v___y_1022_ = v___y_959_;
v___y_1023_ = v___y_960_;
v___y_1024_ = v___y_961_;
v___y_1025_ = v___y_962_;
v___y_1026_ = v___y_963_;
v___y_1027_ = v___y_964_;
v___y_1028_ = v___y_965_;
v___y_1029_ = v___y_966_;
v___y_1030_ = v___y_967_;
goto v___jp_1018_;
}
}
}
else
{
lean_del_object(v___x_1016_);
lean_dec(v_a_1014_);
v___y_1019_ = v___y_957_;
v_postCondEntailsMkRule_1020_ = v_postCondEntailsMkRule_1011_;
v___y_1021_ = v___y_958_;
v___y_1022_ = v___y_959_;
v___y_1023_ = v___y_960_;
v___y_1024_ = v___y_961_;
v___y_1025_ = v___y_962_;
v___y_1026_ = v___y_963_;
v___y_1027_ = v___y_964_;
v___y_1028_ = v___y_965_;
v___y_1029_ = v___y_966_;
v___y_1030_ = v___y_967_;
goto v___jp_1018_;
}
v___jp_1018_:
{
lean_object* v___x_1031_; 
lean_inc_ref(v_postCondEntailsMkRule_1020_);
v___x_1031_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_postCondEntailsMkRule_1020_, v_goal_956_, v___x_1012_, v___y_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
if (lean_obj_tag(v_a_1032_) == 1)
{
lean_object* v_mvarIds_1033_; 
v_mvarIds_1033_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_mvarIds_1033_);
lean_dec_ref_known(v_a_1032_, 1);
if (lean_obj_tag(v_mvarIds_1033_) == 1)
{
lean_object* v_tail_1034_; 
v_tail_1034_ = lean_ctor_get(v_mvarIds_1033_, 1);
lean_inc(v_tail_1034_);
if (lean_obj_tag(v_tail_1034_) == 1)
{
lean_object* v_tail_1035_; 
v_tail_1035_ = lean_ctor_get(v_tail_1034_, 1);
lean_inc(v_tail_1035_);
if (lean_obj_tag(v_tail_1035_) == 0)
{
lean_object* v_head_1036_; lean_object* v_head_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_976_);
v_head_1036_ = lean_ctor_get(v_mvarIds_1033_, 0);
lean_inc(v_head_1036_);
lean_dec_ref_known(v_mvarIds_1033_, 2);
v_head_1037_ = lean_ctor_get(v_tail_1034_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_tail_1034_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_tail_1034_, 1);
lean_dec(v_unused_1069_);
v___x_1039_ = v_tail_1034_;
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_head_1037_);
lean_dec(v_tail_1034_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc(v_head_1037_);
v___x_1041_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed), 13, 1);
lean_closure_set(v___x_1041_, 0, v_head_1037_);
v___x_1042_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_1037_, v___x_1041_, v___y_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
lean_inc(v_head_1036_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed), 16, 4);
lean_closure_set(v___f_1044_, 0, v_head_1036_);
lean_closure_set(v___f_1044_, 1, v___x_1005_);
lean_closure_set(v___f_1044_, 2, v___x_1006_);
lean_closure_set(v___f_1044_, 3, v___x_1007_);
v___x_1045_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_1036_, v___f_1044_, v___y_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1045_) == 0)
{
if (lean_obj_tag(v_a_1043_) == 0)
{
lean_object* v_a_1046_; 
lean_del_object(v___x_1039_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___y_970_ = v_a_1046_;
v___y_971_ = v_tail_1035_;
goto v___jp_969_;
}
else
{
lean_object* v_a_1047_; lean_object* v_val_1048_; lean_object* v___x_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1045_, 1);
v_val_1048_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_a_1043_, 1);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_val_1048_);
v___x_1050_ = v___x_1039_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_tail_1035_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
v___y_970_ = v_a_1047_;
v___y_971_ = v___x_1050_;
goto v___jp_969_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_a_1043_);
lean_del_object(v___x_1039_);
v_a_1052_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1045_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1045_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_del_object(v___x_1039_);
lean_dec(v_head_1036_);
v_a_1060_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1042_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1042_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_1034_, 2);
lean_dec(v_tail_1035_);
lean_dec_ref_known(v_mvarIds_1033_, 2);
v___y_986_ = v___y_1027_;
v___y_987_ = v___y_1028_;
v___y_988_ = v___y_1029_;
v___y_989_ = v___y_1030_;
goto v___jp_985_;
}
}
else
{
lean_dec(v_tail_1034_);
lean_dec_ref_known(v_mvarIds_1033_, 2);
v___y_986_ = v___y_1027_;
v___y_987_ = v___y_1028_;
v___y_988_ = v___y_1029_;
v___y_989_ = v___y_1030_;
goto v___jp_985_;
}
}
else
{
lean_dec(v_mvarIds_1033_);
v___y_986_ = v___y_1027_;
v___y_987_ = v___y_1028_;
v___y_988_ = v___y_1029_;
v___y_989_ = v___y_1030_;
goto v___jp_985_;
}
}
else
{
lean_dec(v_a_1032_);
v___y_986_ = v___y_1027_;
v___y_987_ = v___y_1028_;
v___y_988_ = v___y_1029_;
v___y_989_ = v___y_1030_;
goto v___jp_985_;
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_a_976_);
v_a_1070_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1031_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1031_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_976_);
lean_dec(v_goal_956_);
v_a_1090_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1013_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1013_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
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
v___jp_980_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
v___jp_985_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_990_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4);
v___x_991_ = l_Lean_MessageData_ofExpr(v_a_976_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_994_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_995_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_goal_956_);
v_a_1099_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_975_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_975_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
v___jp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v___y_970_);
lean_ctor_set(v___x_972_, 1, v___y_971_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed(lean_object* v_goal_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(v_goal_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(lean_object* v_goal_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___f_1134_; lean_object* v___x_1135_; 
lean_inc(v_goal_1121_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed), 13, 1);
lean_closure_set(v___f_1134_, 0, v_goal_1121_);
v___x_1135_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_1121_, v___f_1134_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___boxed(lean_object* v_goal_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(v_goal_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4(void){
_start:
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = 0;
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3));
v___x_1161_ = l_Lean_MessageData_ofConstName(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4);
v___x_1163_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(lean_object* v_goal_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_goal_1179_; lean_object* v_entailsConsIntroRule_1182_; lean_object* v_applyPureConsEntailsLRule_1183_; lean_object* v_applyPureConsEntailsRRule_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_entailsConsIntroRule_1182_ = lean_ctor_get(v_a_1166_, 0);
v_applyPureConsEntailsLRule_1183_ = lean_ctor_get(v_a_1166_, 3);
v_applyPureConsEntailsRRule_1184_ = lean_ctor_get(v_a_1166_, 4);
v___x_1185_ = lean_box(0);
lean_inc_ref(v_entailsConsIntroRule_1182_);
v___x_1186_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsConsIntroRule_1182_, v_goal_1165_, v___x_1185_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1248_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1248_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1248_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
if (lean_obj_tag(v_a_1187_) == 1)
{
lean_object* v_mvarIds_1195_; 
v_mvarIds_1195_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_mvarIds_1195_);
lean_dec_ref_known(v_a_1187_, 1);
if (lean_obj_tag(v_mvarIds_1195_) == 1)
{
lean_object* v_tail_1196_; 
v_tail_1196_ = lean_ctor_get(v_mvarIds_1195_, 1);
if (lean_obj_tag(v_tail_1196_) == 0)
{
lean_object* v_head_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_del_object(v___x_1189_);
v_head_1197_ = lean_ctor_get(v_mvarIds_1195_, 0);
lean_inc(v_head_1197_);
lean_dec_ref_known(v_mvarIds_1195_, 2);
v___x_1198_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5);
v___x_1199_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_1197_, v___x_1198_, v_a_1166_, v_a_1167_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_n(v_a_1200_, 2);
lean_dec_ref_known(v___x_1199_, 1);
lean_inc_ref(v_applyPureConsEntailsLRule_1183_);
v___x_1201_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_applyPureConsEntailsLRule_1183_, v_a_1200_, v___x_1185_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v_goal_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1201_, 1);
if (lean_obj_tag(v_a_1202_) == 1)
{
lean_object* v_mvarIds_1229_; 
v_mvarIds_1229_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_mvarIds_1229_);
lean_dec_ref_known(v_a_1202_, 1);
if (lean_obj_tag(v_mvarIds_1229_) == 1)
{
lean_object* v_tail_1230_; 
v_tail_1230_ = lean_ctor_get(v_mvarIds_1229_, 1);
if (lean_obj_tag(v_tail_1230_) == 0)
{
lean_object* v_head_1231_; 
lean_dec(v_a_1200_);
v_head_1231_ = lean_ctor_get(v_mvarIds_1229_, 0);
lean_inc(v_head_1231_);
lean_dec_ref_known(v_mvarIds_1229_, 2);
v_goal_1204_ = v_head_1231_;
v___y_1205_ = v_a_1166_;
v___y_1206_ = v_a_1167_;
v___y_1207_ = v_a_1168_;
v___y_1208_ = v_a_1169_;
v___y_1209_ = v_a_1170_;
v___y_1210_ = v_a_1171_;
v___y_1211_ = v_a_1172_;
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1203_;
}
else
{
lean_dec_ref_known(v_mvarIds_1229_, 2);
v_goal_1204_ = v_a_1200_;
v___y_1205_ = v_a_1166_;
v___y_1206_ = v_a_1167_;
v___y_1207_ = v_a_1168_;
v___y_1208_ = v_a_1169_;
v___y_1209_ = v_a_1170_;
v___y_1210_ = v_a_1171_;
v___y_1211_ = v_a_1172_;
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1203_;
}
}
else
{
lean_dec(v_mvarIds_1229_);
v_goal_1204_ = v_a_1200_;
v___y_1205_ = v_a_1166_;
v___y_1206_ = v_a_1167_;
v___y_1207_ = v_a_1168_;
v___y_1208_ = v_a_1169_;
v___y_1209_ = v_a_1170_;
v___y_1210_ = v_a_1171_;
v___y_1211_ = v_a_1172_;
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1203_;
}
}
else
{
lean_dec(v_a_1202_);
v_goal_1204_ = v_a_1200_;
v___y_1205_ = v_a_1166_;
v___y_1206_ = v_a_1167_;
v___y_1207_ = v_a_1168_;
v___y_1208_ = v_a_1169_;
v___y_1209_ = v_a_1170_;
v___y_1210_ = v_a_1171_;
v___y_1211_ = v_a_1172_;
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1203_;
}
v___jp_1203_:
{
lean_object* v___x_1216_; 
lean_inc(v_goal_1204_);
lean_inc_ref(v_applyPureConsEntailsRRule_1184_);
v___x_1216_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_applyPureConsEntailsRRule_1184_, v_goal_1204_, v___x_1185_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
if (lean_obj_tag(v_a_1217_) == 1)
{
lean_object* v_mvarIds_1218_; 
v_mvarIds_1218_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_mvarIds_1218_);
lean_dec_ref_known(v_a_1217_, 1);
if (lean_obj_tag(v_mvarIds_1218_) == 1)
{
lean_object* v_tail_1219_; 
v_tail_1219_ = lean_ctor_get(v_mvarIds_1218_, 1);
if (lean_obj_tag(v_tail_1219_) == 0)
{
lean_object* v_head_1220_; 
lean_dec(v_goal_1204_);
v_head_1220_ = lean_ctor_get(v_mvarIds_1218_, 0);
lean_inc(v_head_1220_);
lean_dec_ref_known(v_mvarIds_1218_, 2);
v_goal_1179_ = v_head_1220_;
goto v___jp_1178_;
}
else
{
lean_dec_ref_known(v_mvarIds_1218_, 2);
v_goal_1179_ = v_goal_1204_;
goto v___jp_1178_;
}
}
else
{
lean_dec(v_mvarIds_1218_);
v_goal_1179_ = v_goal_1204_;
goto v___jp_1178_;
}
}
else
{
lean_dec(v_a_1217_);
v_goal_1179_ = v_goal_1204_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_goal_1204_);
v_a_1221_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1216_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1216_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1200_);
v_a_1232_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1201_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1201_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1199_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1199_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1195_, 2);
goto v___jp_1191_;
}
}
else
{
lean_dec(v_mvarIds_1195_);
goto v___jp_1191_;
}
}
else
{
lean_dec(v_a_1187_);
goto v___jp_1191_;
}
v___jp_1191_:
{
lean_object* v___x_1193_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1185_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_a_1249_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1186_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1186_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_goal_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___boxed(lean_object* v_goal_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(v_goal_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1270_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(lean_object* v_a_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1346_; 
v_fst_1293_ = lean_ctor_get(v_a_1280_, 0);
v_snd_1294_ = lean_ctor_get(v_a_1280_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_a_1280_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1296_ = v_a_1280_;
v_isShared_1297_ = v_isSharedCheck_1346_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_inc(v_fst_1293_);
lean_dec(v_a_1280_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1346_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_lt(v___x_1298_, v_fst_1293_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1301_; 
if (v_isShared_1297_ == 0)
{
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_fst_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_snd_1294_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
else
{
lean_object* v___x_1304_; 
lean_inc(v_snd_1294_);
v___x_1304_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(v_snd_1294_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_sub(v_fst_1293_, v___x_1306_);
lean_dec(v_fst_1293_);
if (lean_obj_tag(v_a_1305_) == 1)
{
lean_object* v_val_1308_; lean_object* v___x_1310_; 
lean_dec(v_snd_1294_);
v_val_1308_ = lean_ctor_get(v_a_1305_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v_a_1305_, 1);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v_val_1308_);
lean_ctor_set(v___x_1296_, 0, v___x_1307_);
v___x_1310_ = v___x_1296_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_val_1308_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v_a_1280_ = v___x_1310_;
goto _start;
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_a_1305_);
v___x_1313_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1);
lean_inc(v_snd_1294_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_snd_1294_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_nat_add(v___x_1307_, v___x_1306_);
v___x_1319_ = l_Nat_reprFast(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = l_Lean_MessageData_ofFormat(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1317_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_1324_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1327_; 
lean_dec_ref_known(v___x_1325_, 1);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1307_);
v___x_1327_ = v___x_1296_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_snd_1294_);
v___x_1327_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
v_a_1280_ = v___x_1327_;
goto _start;
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v___x_1307_);
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
v_a_1330_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1325_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
lean_dec(v_fst_1293_);
v_a_1338_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1304_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1304_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___boxed(lean_object* v_a_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(lean_object* v_thm_1361_, lean_object* v_goal_1362_, lean_object* v_excessArgs_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_kind_1376_; 
v_kind_1376_ = lean_ctor_get(v_thm_1361_, 2);
lean_inc_ref(v_kind_1376_);
lean_dec_ref(v_thm_1361_);
if (lean_obj_tag(v_kind_1376_) == 0)
{
lean_object* v_etaPotential_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1411_; 
v_etaPotential_1377_ = lean_ctor_get(v_kind_1376_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_kind_1376_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1379_ = v_kind_1376_;
v_isShared_1380_ = v_isSharedCheck_1411_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_etaPotential_1377_);
lean_dec(v_kind_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1411_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v_n_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1381_ = lean_array_get_size(v_excessArgs_1363_);
v_n_1382_ = lean_nat_sub(v_etaPotential_1377_, v___x_1381_);
lean_dec(v_etaPotential_1377_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_nat_dec_eq(v_n_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_n_1382_);
lean_ctor_set(v___x_1385_, 1, v_goal_1362_);
v___x_1386_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v___x_1385_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_snd_1391_; lean_object* v___x_1393_; 
v_snd_1391_ = lean_ctor_get(v_a_1387_, 1);
lean_inc(v_snd_1391_);
lean_dec(v_a_1387_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 1);
lean_ctor_set(v___x_1379_, 0, v_snd_1391_);
v___x_1393_ = v___x_1379_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_snd_1391_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1379_);
v_a_1399_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1386_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1386_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_n_1382_);
lean_dec(v_goal_1362_);
v___x_1407_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1407_);
v___x_1409_ = v___x_1379_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_kind_1376_);
lean_dec(v_goal_1362_);
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro___boxed(lean_object* v_thm_1414_, lean_object* v_goal_1415_, lean_object* v_excessArgs_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(v_thm_1414_, v_goal_1415_, v_excessArgs_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec_ref(v_excessArgs_1416_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(lean_object* v_inst_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___boxed(lean_object* v_inst_1445_, lean_object* v_a_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(v_inst_1445_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(uint8_t v_progress_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_fst_1474_; lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1505_; 
v_fst_1474_ = lean_ctor_get(v_a_1461_, 0);
v_snd_1475_ = lean_ctor_get(v_a_1461_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_a_1461_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1477_ = v_a_1461_;
v_isShared_1478_ = v_isSharedCheck_1505_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_inc(v_fst_1474_);
lean_dec(v_a_1461_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1505_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; 
lean_inc(v_snd_1475_);
v___x_1479_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(v_snd_1475_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1496_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1496_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1496_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
if (lean_obj_tag(v_a_1480_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_del_object(v___x_1482_);
lean_dec(v_snd_1475_);
lean_dec(v_fst_1474_);
v_val_1484_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_a_1480_, 1);
v___x_1485_ = lean_box(v_progress_1460_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v_val_1484_);
lean_ctor_set(v___x_1477_, 0, v___x_1485_);
v___x_1487_ = v___x_1477_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_val_1484_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v_a_1461_ = v___x_1487_;
goto _start;
}
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_a_1480_);
if (v_isShared_1478_ == 0)
{
v___x_1491_ = v___x_1477_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_fst_1474_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1475_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1491_);
v___x_1493_ = v___x_1482_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1477_);
lean_dec(v_snd_1475_);
lean_dec(v_fst_1474_);
v_a_1497_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1479_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1479_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg___boxed(lean_object* v_progress_1506_, lean_object* v_a_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_progress_boxed_1520_; lean_object* v_res_1521_; 
v_progress_boxed_1520_ = lean_unbox(v_progress_1506_);
v_res_1521_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_boxed_1520_, v_a_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2(void){
_start:
{
uint8_t v_progress_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_progress_1528_ = 0;
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1));
v___x_1530_ = l_Lean_MessageData_ofConstName(v___x_1529_, v_progress_1528_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1531_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8(void){
_start:
{
uint8_t v_progress_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_progress_1546_ = 0;
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7));
v___x_1548_ = l_Lean_MessageData_ofConstName(v___x_1547_, v_progress_1546_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8);
v___x_1550_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15(void){
_start:
{
uint8_t v_progress_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_progress_1562_ = 0;
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14));
v___x_1564_ = l_Lean_MessageData_ofConstName(v___x_1563_, v_progress_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15);
v___x_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___x_1565_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8);
v___x_1569_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v___x_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2);
v___x_1572_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8);
v___x_1575_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20));
v___x_1581_ = l_Lean_mkConst(v___x_1580_, v___x_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(lean_object* v_goal_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v_progress_1598_; lean_object* v_goal_1599_; uint8_t v___y_1605_; uint8_t v_progress_1606_; lean_object* v_goal_1607_; lean_object* v___y_1608_; lean_object* v_downPureIntroRule_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; uint8_t v___y_1635_; uint8_t v_progress_1636_; lean_object* v_goal_1637_; lean_object* v___y_1638_; lean_object* v_downPureIntroRule_1639_; lean_object* v_pureIntroRule_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___x_1685_; 
lean_inc(v_goal_1584_);
v___x_1685_ = l_Lean_MVarId_getType(v_goal_1584_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_2047_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_2047_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_2047_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = l_Lean_Expr_cleanupAnnotations(v_a_1686_);
v___x_1696_ = l_Lean_Expr_isApp(v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v___x_1695_);
lean_dec(v_goal_1584_);
goto v___jp_1690_;
}
else
{
lean_object* v_arg_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_arg_1697_ = lean_ctor_get(v___x_1695_, 1);
lean_inc_ref(v_arg_1697_);
v___x_1698_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1695_);
v___x_1699_ = l_Lean_Expr_isApp(v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v___x_1698_);
lean_dec_ref(v_arg_1697_);
lean_dec(v_goal_1584_);
goto v___jp_1690_;
}
else
{
lean_object* v_arg_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_arg_1700_ = lean_ctor_get(v___x_1698_, 1);
lean_inc_ref(v_arg_1700_);
v___x_1701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1698_);
v___x_1702_ = l_Lean_Expr_isApp(v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec_ref(v___x_1701_);
lean_dec_ref(v_arg_1700_);
lean_dec_ref(v_arg_1697_);
lean_dec(v_goal_1584_);
goto v___jp_1690_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v_progress_1705_; 
v___x_1703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1701_);
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6));
v_progress_1705_ = l_Lean_Expr_isConstOf(v___x_1703_, v___x_1704_);
lean_dec_ref(v___x_1703_);
if (v_progress_1705_ == 0)
{
lean_dec_ref(v_arg_1700_);
lean_dec_ref(v_arg_1697_);
lean_dec(v_goal_1584_);
goto v___jp_1690_;
}
else
{
uint8_t v_progress_1706_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___x_1753_; lean_object* v___y_1755_; uint8_t v_progress_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1879_; uint8_t v_progress_1880_; lean_object* v_goal_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v_progress_1926_; lean_object* v_goal_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1976_; lean_object* v___y_1977_; uint8_t v_pureHNonTrue_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2036_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
lean_del_object(v___x_1688_);
v_progress_1706_ = 0;
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5));
v___x_2042_ = lean_unsigned_to_nat(2u);
v___x_2043_ = l_Lean_Expr_isAppOfArity(v_arg_1700_, v___x_1753_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref(v_arg_1700_);
v___x_2044_ = lean_box(0);
v___y_2036_ = v___x_2044_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = l_Lean_Expr_appArg_x21(v_arg_1700_);
lean_dec_ref(v_arg_1700_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___y_2036_ = v___x_2046_;
goto v___jp_2035_;
}
v___jp_1707_:
{
lean_object* v_downPureIntroRule_1722_; lean_object* v_pureElimRule_1723_; lean_object* v_pureIntroRule_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_downPureIntroRule_1722_ = lean_ctor_get(v___y_1709_, 5);
v_pureElimRule_1723_ = lean_ctor_get(v___y_1709_, 6);
v_pureIntroRule_1724_ = lean_ctor_get(v___y_1709_, 7);
v___x_1725_ = lean_box(0);
lean_inc(v___y_1721_);
lean_inc_ref(v_pureElimRule_1723_);
v___x_1726_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_pureElimRule_1723_, v___y_1721_, v___x_1725_, v___y_1709_, v___y_1711_, v___y_1710_, v___y_1720_, v___y_1708_, v___y_1715_, v___y_1718_, v___y_1716_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
if (lean_obj_tag(v_a_1727_) == 1)
{
lean_object* v_mvarIds_1728_; 
v_mvarIds_1728_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_mvarIds_1728_);
lean_dec_ref_known(v_a_1727_, 1);
if (lean_obj_tag(v_mvarIds_1728_) == 1)
{
lean_object* v_tail_1729_; 
v_tail_1729_ = lean_ctor_get(v_mvarIds_1728_, 1);
if (lean_obj_tag(v_tail_1729_) == 0)
{
lean_object* v_head_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v___y_1721_);
lean_dec(v___y_1719_);
v_head_1730_ = lean_ctor_get(v_mvarIds_1728_, 0);
lean_inc(v_head_1730_);
lean_dec_ref_known(v_mvarIds_1728_, 2);
v___x_1731_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
v___x_1732_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_1730_, v___x_1731_, v___y_1709_, v___y_1711_, v___y_1715_, v___y_1718_, v___y_1716_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___y_1635_ = v___y_1717_;
v_progress_1636_ = v___y_1717_;
v_goal_1637_ = v_a_1733_;
v___y_1638_ = v___y_1709_;
v_downPureIntroRule_1639_ = v_downPureIntroRule_1722_;
v_pureIntroRule_1640_ = v_pureIntroRule_1724_;
v___y_1641_ = v___y_1711_;
v___y_1642_ = v___y_1710_;
v___y_1643_ = v___y_1720_;
v___y_1644_ = v___y_1708_;
v___y_1645_ = v___y_1715_;
v___y_1646_ = v___y_1718_;
v___y_1647_ = v___y_1716_;
v___y_1648_ = v___y_1712_;
v___y_1649_ = v___y_1713_;
v___y_1650_ = v___y_1714_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1734_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1732_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
uint8_t v___x_1742_; 
lean_dec_ref_known(v_mvarIds_1728_, 2);
v___x_1742_ = lean_unbox(v___y_1719_);
lean_dec(v___y_1719_);
v___y_1635_ = v___y_1717_;
v_progress_1636_ = v___x_1742_;
v_goal_1637_ = v___y_1721_;
v___y_1638_ = v___y_1709_;
v_downPureIntroRule_1639_ = v_downPureIntroRule_1722_;
v_pureIntroRule_1640_ = v_pureIntroRule_1724_;
v___y_1641_ = v___y_1711_;
v___y_1642_ = v___y_1710_;
v___y_1643_ = v___y_1720_;
v___y_1644_ = v___y_1708_;
v___y_1645_ = v___y_1715_;
v___y_1646_ = v___y_1718_;
v___y_1647_ = v___y_1716_;
v___y_1648_ = v___y_1712_;
v___y_1649_ = v___y_1713_;
v___y_1650_ = v___y_1714_;
goto v___jp_1634_;
}
}
else
{
uint8_t v___x_1743_; 
lean_dec(v_mvarIds_1728_);
v___x_1743_ = lean_unbox(v___y_1719_);
lean_dec(v___y_1719_);
v___y_1635_ = v___y_1717_;
v_progress_1636_ = v___x_1743_;
v_goal_1637_ = v___y_1721_;
v___y_1638_ = v___y_1709_;
v_downPureIntroRule_1639_ = v_downPureIntroRule_1722_;
v_pureIntroRule_1640_ = v_pureIntroRule_1724_;
v___y_1641_ = v___y_1711_;
v___y_1642_ = v___y_1710_;
v___y_1643_ = v___y_1720_;
v___y_1644_ = v___y_1708_;
v___y_1645_ = v___y_1715_;
v___y_1646_ = v___y_1718_;
v___y_1647_ = v___y_1716_;
v___y_1648_ = v___y_1712_;
v___y_1649_ = v___y_1713_;
v___y_1650_ = v___y_1714_;
goto v___jp_1634_;
}
}
else
{
uint8_t v___x_1744_; 
lean_dec(v_a_1727_);
v___x_1744_ = lean_unbox(v___y_1719_);
lean_dec(v___y_1719_);
v___y_1635_ = v___y_1717_;
v_progress_1636_ = v___x_1744_;
v_goal_1637_ = v___y_1721_;
v___y_1638_ = v___y_1709_;
v_downPureIntroRule_1639_ = v_downPureIntroRule_1722_;
v_pureIntroRule_1640_ = v_pureIntroRule_1724_;
v___y_1641_ = v___y_1711_;
v___y_1642_ = v___y_1710_;
v___y_1643_ = v___y_1720_;
v___y_1644_ = v___y_1708_;
v___y_1645_ = v___y_1715_;
v___y_1646_ = v___y_1718_;
v___y_1647_ = v___y_1716_;
v___y_1648_ = v___y_1712_;
v___y_1649_ = v___y_1713_;
v___y_1650_ = v___y_1714_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v___y_1721_);
lean_dec(v___y_1719_);
v_a_1745_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1726_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1726_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_box(v_progress_1756_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___y_1755_);
v___x_1770_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_1705_, v___x_1769_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1774_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_fst_1772_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v_a_1771_, 1);
lean_inc_n(v_snd_1773_, 2);
lean_dec(v_a_1771_);
v___x_1774_ = l_Lean_MVarId_getType(v_snd_1773_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_Expr_cleanupAnnotations(v_a_1775_);
v___x_1777_ = l_Lean_Expr_isApp(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___x_1776_);
lean_dec(v_fst_1772_);
v___y_1666_ = v_snd_1773_;
v___y_1667_ = v___y_1764_;
v___y_1668_ = v___y_1765_;
v___y_1669_ = v___y_1766_;
v___y_1670_ = v___y_1767_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1776_);
v___x_1779_ = l_Lean_Expr_isApp(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v___x_1778_);
lean_dec(v_fst_1772_);
v___y_1666_ = v_snd_1773_;
v___y_1667_ = v___y_1764_;
v___y_1668_ = v___y_1765_;
v___y_1669_ = v___y_1766_;
v___y_1670_ = v___y_1767_;
goto v___jp_1665_;
}
else
{
lean_object* v_arg_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_arg_1780_ = lean_ctor_get(v___x_1778_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1778_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v_arg_1780_);
lean_dec(v_fst_1772_);
v___y_1666_ = v_snd_1773_;
v___y_1667_ = v___y_1764_;
v___y_1668_ = v___y_1765_;
v___y_1669_ = v___y_1766_;
v___y_1670_ = v___y_1767_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1781_);
v___x_1784_ = l_Lean_Expr_isConstOf(v___x_1783_, v___x_1704_);
lean_dec_ref(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v_arg_1780_);
lean_dec(v_fst_1772_);
v___y_1666_ = v_snd_1773_;
v___y_1667_ = v___y_1764_;
v___y_1668_ = v___y_1765_;
v___y_1669_ = v___y_1766_;
v___y_1670_ = v___y_1767_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(2u);
v___x_1786_ = l_Lean_Expr_isAppOfArity(v_arg_1780_, v___x_1753_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v_entailsNilIntroRule_1787_; lean_object* v_downPureIntroRule_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_arg_1780_);
v_entailsNilIntroRule_1787_ = lean_ctor_get(v___y_1757_, 2);
v_downPureIntroRule_1788_ = lean_ctor_get(v___y_1757_, 5);
v___x_1789_ = lean_box(0);
lean_inc(v_snd_1773_);
lean_inc_ref(v_entailsNilIntroRule_1787_);
v___x_1790_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsNilIntroRule_1787_, v_snd_1773_, v___x_1789_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
if (lean_obj_tag(v_a_1791_) == 1)
{
lean_object* v_mvarIds_1792_; 
v_mvarIds_1792_ = lean_ctor_get(v_a_1791_, 0);
lean_inc(v_mvarIds_1792_);
lean_dec_ref_known(v_a_1791_, 1);
if (lean_obj_tag(v_mvarIds_1792_) == 1)
{
lean_object* v_tail_1793_; 
v_tail_1793_ = lean_ctor_get(v_mvarIds_1792_, 1);
if (lean_obj_tag(v_tail_1793_) == 0)
{
lean_object* v_head_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_snd_1773_);
lean_dec(v_fst_1772_);
v_head_1794_ = lean_ctor_get(v_mvarIds_1792_, 0);
lean_inc(v_head_1794_);
lean_dec_ref_known(v_mvarIds_1792_, 2);
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9);
v___x_1796_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_1794_, v___x_1795_, v___y_1757_, v___y_1758_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1605_ = v___x_1784_;
v_progress_1606_ = v___x_1784_;
v_goal_1607_ = v_a_1797_;
v___y_1608_ = v___y_1757_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1788_;
v___y_1610_ = v___y_1758_;
v___y_1611_ = v___y_1759_;
v___y_1612_ = v___y_1760_;
v___y_1613_ = v___y_1761_;
v___y_1614_ = v___y_1762_;
v___y_1615_ = v___y_1763_;
v___y_1616_ = v___y_1764_;
v___y_1617_ = v___y_1765_;
v___y_1618_ = v___y_1766_;
v___y_1619_ = v___y_1767_;
goto v___jp_1604_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_a_1798_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1796_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
uint8_t v___x_1806_; 
lean_dec_ref_known(v_mvarIds_1792_, 2);
v___x_1806_ = lean_unbox(v_fst_1772_);
lean_dec(v_fst_1772_);
v___y_1605_ = v___x_1784_;
v_progress_1606_ = v___x_1806_;
v_goal_1607_ = v_snd_1773_;
v___y_1608_ = v___y_1757_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1788_;
v___y_1610_ = v___y_1758_;
v___y_1611_ = v___y_1759_;
v___y_1612_ = v___y_1760_;
v___y_1613_ = v___y_1761_;
v___y_1614_ = v___y_1762_;
v___y_1615_ = v___y_1763_;
v___y_1616_ = v___y_1764_;
v___y_1617_ = v___y_1765_;
v___y_1618_ = v___y_1766_;
v___y_1619_ = v___y_1767_;
goto v___jp_1604_;
}
}
else
{
uint8_t v___x_1807_; 
lean_dec(v_mvarIds_1792_);
v___x_1807_ = lean_unbox(v_fst_1772_);
lean_dec(v_fst_1772_);
v___y_1605_ = v___x_1784_;
v_progress_1606_ = v___x_1807_;
v_goal_1607_ = v_snd_1773_;
v___y_1608_ = v___y_1757_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1788_;
v___y_1610_ = v___y_1758_;
v___y_1611_ = v___y_1759_;
v___y_1612_ = v___y_1760_;
v___y_1613_ = v___y_1761_;
v___y_1614_ = v___y_1762_;
v___y_1615_ = v___y_1763_;
v___y_1616_ = v___y_1764_;
v___y_1617_ = v___y_1765_;
v___y_1618_ = v___y_1766_;
v___y_1619_ = v___y_1767_;
goto v___jp_1604_;
}
}
else
{
uint8_t v___x_1808_; 
lean_dec(v_a_1791_);
v___x_1808_ = lean_unbox(v_fst_1772_);
lean_dec(v_fst_1772_);
v___y_1605_ = v___x_1784_;
v_progress_1606_ = v___x_1808_;
v_goal_1607_ = v_snd_1773_;
v___y_1608_ = v___y_1757_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1788_;
v___y_1610_ = v___y_1758_;
v___y_1611_ = v___y_1759_;
v___y_1612_ = v___y_1760_;
v___y_1613_ = v___y_1761_;
v___y_1614_ = v___y_1762_;
v___y_1615_ = v___y_1763_;
v___y_1616_ = v___y_1764_;
v___y_1617_ = v___y_1765_;
v___y_1618_ = v___y_1766_;
v___y_1619_ = v___y_1767_;
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_snd_1773_);
lean_dec(v_fst_1772_);
v_a_1809_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1790_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1790_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Expr_appArg_x21(v_arg_1780_);
lean_dec_ref(v_arg_1780_);
if (lean_obj_tag(v___x_1817_) == 4)
{
lean_object* v_declName_1818_; 
v_declName_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_declName_1818_);
lean_dec_ref_known(v___x_1817_, 2);
if (lean_obj_tag(v_declName_1818_) == 1)
{
lean_object* v_pre_1819_; 
v_pre_1819_ = lean_ctor_get(v_declName_1818_, 0);
if (lean_obj_tag(v_pre_1819_) == 0)
{
lean_object* v_str_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_str_1820_ = lean_ctor_get(v_declName_1818_, 1);
lean_inc_ref(v_str_1820_);
lean_dec_ref_known(v_declName_1818_, 2);
v___x_1821_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10));
v___x_1822_ = lean_string_dec_eq(v_str_1820_, v___x_1821_);
lean_dec_ref(v_str_1820_);
if (v___x_1822_ == 0)
{
v___y_1708_ = v___y_1761_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1758_;
v___y_1712_ = v___y_1765_;
v___y_1713_ = v___y_1766_;
v___y_1714_ = v___y_1767_;
v___y_1715_ = v___y_1762_;
v___y_1716_ = v___y_1764_;
v___y_1717_ = v___x_1784_;
v___y_1718_ = v___y_1763_;
v___y_1719_ = v_fst_1772_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v_snd_1773_;
goto v___jp_1707_;
}
else
{
if (v___x_1784_ == 0)
{
v___y_1708_ = v___y_1761_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1758_;
v___y_1712_ = v___y_1765_;
v___y_1713_ = v___y_1766_;
v___y_1714_ = v___y_1767_;
v___y_1715_ = v___y_1762_;
v___y_1716_ = v___y_1764_;
v___y_1717_ = v___x_1784_;
v___y_1718_ = v___y_1763_;
v___y_1719_ = v_fst_1772_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v_snd_1773_;
goto v___jp_1707_;
}
else
{
lean_object* v_downPureIntroRule_1823_; lean_object* v_pureIntroRule_1824_; uint8_t v___x_1825_; 
v_downPureIntroRule_1823_ = lean_ctor_get(v___y_1757_, 5);
v_pureIntroRule_1824_ = lean_ctor_get(v___y_1757_, 7);
v___x_1825_ = lean_unbox(v_fst_1772_);
lean_dec(v_fst_1772_);
v___y_1635_ = v___x_1784_;
v_progress_1636_ = v___x_1825_;
v_goal_1637_ = v_snd_1773_;
v___y_1638_ = v___y_1757_;
v_downPureIntroRule_1639_ = v_downPureIntroRule_1823_;
v_pureIntroRule_1640_ = v_pureIntroRule_1824_;
v___y_1641_ = v___y_1758_;
v___y_1642_ = v___y_1759_;
v___y_1643_ = v___y_1760_;
v___y_1644_ = v___y_1761_;
v___y_1645_ = v___y_1762_;
v___y_1646_ = v___y_1763_;
v___y_1647_ = v___y_1764_;
v___y_1648_ = v___y_1765_;
v___y_1649_ = v___y_1766_;
v___y_1650_ = v___y_1767_;
goto v___jp_1634_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1818_, 2);
v___y_1708_ = v___y_1761_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1758_;
v___y_1712_ = v___y_1765_;
v___y_1713_ = v___y_1766_;
v___y_1714_ = v___y_1767_;
v___y_1715_ = v___y_1762_;
v___y_1716_ = v___y_1764_;
v___y_1717_ = v___x_1784_;
v___y_1718_ = v___y_1763_;
v___y_1719_ = v_fst_1772_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v_snd_1773_;
goto v___jp_1707_;
}
}
else
{
lean_dec(v_declName_1818_);
v___y_1708_ = v___y_1761_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1758_;
v___y_1712_ = v___y_1765_;
v___y_1713_ = v___y_1766_;
v___y_1714_ = v___y_1767_;
v___y_1715_ = v___y_1762_;
v___y_1716_ = v___y_1764_;
v___y_1717_ = v___x_1784_;
v___y_1718_ = v___y_1763_;
v___y_1719_ = v_fst_1772_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v_snd_1773_;
goto v___jp_1707_;
}
}
else
{
lean_dec_ref(v___x_1817_);
v___y_1708_ = v___y_1761_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1758_;
v___y_1712_ = v___y_1765_;
v___y_1713_ = v___y_1766_;
v___y_1714_ = v___y_1767_;
v___y_1715_ = v___y_1762_;
v___y_1716_ = v___y_1764_;
v___y_1717_ = v___x_1784_;
v___y_1718_ = v___y_1763_;
v___y_1719_ = v_fst_1772_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v_snd_1773_;
goto v___jp_1707_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_snd_1773_);
lean_dec(v_fst_1772_);
v_a_1826_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1774_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1774_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1770_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1770_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_MVarId_getType(v___y_1844_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17);
v___x_1859_ = l_Lean_MessageData_ofExpr(v_a_1857_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_1860_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1856_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1856_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
v___jp_1878_:
{
if (v_progress_1705_ == 0)
{
lean_dec(v___y_1879_);
v___y_1755_ = v_goal_1881_;
v_progress_1756_ = v_progress_1880_;
v___y_1757_ = v___y_1882_;
v___y_1758_ = v___y_1883_;
v___y_1759_ = v___y_1884_;
v___y_1760_ = v___y_1885_;
v___y_1761_ = v___y_1886_;
v___y_1762_ = v___y_1887_;
v___y_1763_ = v___y_1888_;
v___y_1764_ = v___y_1889_;
v___y_1765_ = v___y_1890_;
v___y_1766_ = v___y_1891_;
v___y_1767_ = v___y_1892_;
goto v___jp_1754_;
}
else
{
if (lean_obj_tag(v___y_1879_) == 0)
{
v___y_1755_ = v_goal_1881_;
v_progress_1756_ = v_progress_1880_;
v___y_1757_ = v___y_1882_;
v___y_1758_ = v___y_1883_;
v___y_1759_ = v___y_1884_;
v___y_1760_ = v___y_1885_;
v___y_1761_ = v___y_1886_;
v___y_1762_ = v___y_1887_;
v___y_1763_ = v___y_1888_;
v___y_1764_ = v___y_1889_;
v___y_1765_ = v___y_1890_;
v___y_1766_ = v___y_1891_;
v___y_1767_ = v___y_1892_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v___y_1879_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___y_1879_, 0);
lean_dec(v_unused_1922_);
v___x_1894_ = v___y_1879_;
v_isShared_1895_ = v_isSharedCheck_1921_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v___y_1879_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1921_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_pureIntroRule_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_pureIntroRule_1896_ = lean_ctor_get(v___y_1882_, 7);
v___x_1897_ = lean_box(0);
lean_inc(v_goal_1881_);
lean_inc_ref(v_pureIntroRule_1896_);
v___x_1898_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_pureIntroRule_1896_, v_goal_1881_, v___x_1897_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1912_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1912_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1912_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
if (lean_obj_tag(v_a_1899_) == 1)
{
lean_object* v_mvarIds_1903_; 
v_mvarIds_1903_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_mvarIds_1903_);
lean_dec_ref_known(v_a_1899_, 1);
if (lean_obj_tag(v_mvarIds_1903_) == 1)
{
lean_object* v_tail_1904_; 
v_tail_1904_ = lean_ctor_get(v_mvarIds_1903_, 1);
if (lean_obj_tag(v_tail_1904_) == 0)
{
lean_object* v_head_1905_; lean_object* v___x_1907_; 
lean_dec(v_goal_1881_);
v_head_1905_ = lean_ctor_get(v_mvarIds_1903_, 0);
lean_inc(v_head_1905_);
lean_dec_ref_known(v_mvarIds_1903_, 2);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_head_1905_);
v___x_1907_ = v___x_1894_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_head_1905_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1907_);
v___x_1909_ = v___x_1901_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1903_, 2);
lean_del_object(v___x_1901_);
lean_del_object(v___x_1894_);
v___y_1843_ = v_progress_1880_;
v___y_1844_ = v_goal_1881_;
v___y_1845_ = v___y_1882_;
v___y_1846_ = v___y_1883_;
v___y_1847_ = v___y_1884_;
v___y_1848_ = v___y_1885_;
v___y_1849_ = v___y_1886_;
v___y_1850_ = v___y_1887_;
v___y_1851_ = v___y_1888_;
v___y_1852_ = v___y_1889_;
v___y_1853_ = v___y_1890_;
v___y_1854_ = v___y_1891_;
v___y_1855_ = v___y_1892_;
goto v___jp_1842_;
}
}
else
{
lean_dec(v_mvarIds_1903_);
lean_del_object(v___x_1901_);
lean_del_object(v___x_1894_);
v___y_1843_ = v_progress_1880_;
v___y_1844_ = v_goal_1881_;
v___y_1845_ = v___y_1882_;
v___y_1846_ = v___y_1883_;
v___y_1847_ = v___y_1884_;
v___y_1848_ = v___y_1885_;
v___y_1849_ = v___y_1886_;
v___y_1850_ = v___y_1887_;
v___y_1851_ = v___y_1888_;
v___y_1852_ = v___y_1889_;
v___y_1853_ = v___y_1890_;
v___y_1854_ = v___y_1891_;
v___y_1855_ = v___y_1892_;
goto v___jp_1842_;
}
}
else
{
lean_del_object(v___x_1901_);
lean_dec(v_a_1899_);
lean_del_object(v___x_1894_);
v___y_1843_ = v_progress_1880_;
v___y_1844_ = v_goal_1881_;
v___y_1845_ = v___y_1882_;
v___y_1846_ = v___y_1883_;
v___y_1847_ = v___y_1884_;
v___y_1848_ = v___y_1885_;
v___y_1849_ = v___y_1886_;
v___y_1850_ = v___y_1887_;
v___y_1851_ = v___y_1888_;
v___y_1852_ = v___y_1889_;
v___y_1853_ = v___y_1890_;
v___y_1854_ = v___y_1891_;
v___y_1855_ = v___y_1892_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_del_object(v___x_1894_);
lean_dec(v_goal_1881_);
v_a_1913_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1898_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1898_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
v___jp_1923_:
{
if (lean_obj_tag(v___y_1924_) == 0)
{
lean_dec(v___y_1925_);
v___y_1755_ = v_goal_1927_;
v_progress_1756_ = v_progress_1926_;
v___y_1757_ = v___y_1928_;
v___y_1758_ = v___y_1929_;
v___y_1759_ = v___y_1930_;
v___y_1760_ = v___y_1931_;
v___y_1761_ = v___y_1932_;
v___y_1762_ = v___y_1933_;
v___y_1763_ = v___y_1934_;
v___y_1764_ = v___y_1935_;
v___y_1765_ = v___y_1936_;
v___y_1766_ = v___y_1937_;
v___y_1767_ = v___y_1938_;
goto v___jp_1754_;
}
else
{
lean_dec_ref_known(v___y_1924_, 1);
v___y_1879_ = v___y_1925_;
v_progress_1880_ = v_progress_1926_;
v_goal_1881_ = v_goal_1927_;
v___y_1882_ = v___y_1928_;
v___y_1883_ = v___y_1929_;
v___y_1884_ = v___y_1930_;
v___y_1885_ = v___y_1931_;
v___y_1886_ = v___y_1932_;
v___y_1887_ = v___y_1933_;
v___y_1888_ = v___y_1934_;
v___y_1889_ = v___y_1935_;
v___y_1890_ = v___y_1936_;
v___y_1891_ = v___y_1937_;
v___y_1892_ = v___y_1938_;
goto v___jp_1878_;
}
}
v___jp_1939_:
{
lean_object* v___x_1953_; 
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
v___x_1953_ = l_Lean_MVarId_getType(v_goal_1584_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19);
v___x_1956_ = l_Lean_MessageData_ofExpr(v_a_1954_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_1957_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1953_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1953_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
v___jp_1975_:
{
if (v_pureHNonTrue_1978_ == 0)
{
v___y_1924_ = v___y_1976_;
v___y_1925_ = v___y_1977_;
v_progress_1926_ = v_progress_1706_;
v_goal_1927_ = v_goal_1584_;
v___y_1928_ = v___y_1979_;
v___y_1929_ = v___y_1980_;
v___y_1930_ = v___y_1981_;
v___y_1931_ = v___y_1982_;
v___y_1932_ = v___y_1983_;
v___y_1933_ = v___y_1984_;
v___y_1934_ = v___y_1985_;
v___y_1935_ = v___y_1986_;
v___y_1936_ = v___y_1987_;
v___y_1937_ = v___y_1988_;
v___y_1938_ = v___y_1989_;
goto v___jp_1923_;
}
else
{
lean_object* v_pureElimRule_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_pureElimRule_1990_ = lean_ctor_get(v___y_1979_, 6);
v___x_1991_ = lean_box(0);
lean_inc(v_goal_1584_);
lean_inc_ref(v_pureElimRule_1990_);
v___x_1992_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_pureElimRule_1990_, v_goal_1584_, v___x_1991_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
if (lean_obj_tag(v_a_1993_) == 1)
{
lean_object* v_mvarIds_1994_; 
v_mvarIds_1994_ = lean_ctor_get(v_a_1993_, 0);
lean_inc(v_mvarIds_1994_);
lean_dec_ref_known(v_a_1993_, 1);
if (lean_obj_tag(v_mvarIds_1994_) == 1)
{
lean_object* v_tail_1995_; 
v_tail_1995_ = lean_ctor_get(v_mvarIds_1994_, 1);
if (lean_obj_tag(v_tail_1995_) == 0)
{
lean_object* v_head_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec(v_goal_1584_);
v_head_1996_ = lean_ctor_get(v_mvarIds_1994_, 0);
lean_inc(v_head_1996_);
lean_dec_ref_known(v_mvarIds_1994_, 2);
v___x_1997_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
v___x_1998_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_1996_, v___x_1997_, v___y_1979_, v___y_1980_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1924_ = v___y_1976_;
v___y_1925_ = v___y_1977_;
v_progress_1926_ = v_progress_1705_;
v_goal_1927_ = v_a_1999_;
v___y_1928_ = v___y_1979_;
v___y_1929_ = v___y_1980_;
v___y_1930_ = v___y_1981_;
v___y_1931_ = v___y_1982_;
v___y_1932_ = v___y_1983_;
v___y_1933_ = v___y_1984_;
v___y_1934_ = v___y_1985_;
v___y_1935_ = v___y_1986_;
v___y_1936_ = v___y_1987_;
v___y_1937_ = v___y_1988_;
v___y_1938_ = v___y_1989_;
goto v___jp_1923_;
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v___y_1977_);
lean_dec(v___y_1976_);
v_a_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1994_, 2);
v___y_1940_ = v___y_1976_;
v___y_1941_ = v___y_1977_;
v___y_1942_ = v___y_1979_;
v___y_1943_ = v___y_1980_;
v___y_1944_ = v___y_1981_;
v___y_1945_ = v___y_1982_;
v___y_1946_ = v___y_1983_;
v___y_1947_ = v___y_1984_;
v___y_1948_ = v___y_1985_;
v___y_1949_ = v___y_1986_;
v___y_1950_ = v___y_1987_;
v___y_1951_ = v___y_1988_;
v___y_1952_ = v___y_1989_;
goto v___jp_1939_;
}
}
else
{
lean_dec(v_mvarIds_1994_);
v___y_1940_ = v___y_1976_;
v___y_1941_ = v___y_1977_;
v___y_1942_ = v___y_1979_;
v___y_1943_ = v___y_1980_;
v___y_1944_ = v___y_1981_;
v___y_1945_ = v___y_1982_;
v___y_1946_ = v___y_1983_;
v___y_1947_ = v___y_1984_;
v___y_1948_ = v___y_1985_;
v___y_1949_ = v___y_1986_;
v___y_1950_ = v___y_1987_;
v___y_1951_ = v___y_1988_;
v___y_1952_ = v___y_1989_;
goto v___jp_1939_;
}
}
else
{
lean_dec(v_a_1993_);
v___y_1940_ = v___y_1976_;
v___y_1941_ = v___y_1977_;
v___y_1942_ = v___y_1979_;
v___y_1943_ = v___y_1980_;
v___y_1944_ = v___y_1981_;
v___y_1945_ = v___y_1982_;
v___y_1946_ = v___y_1983_;
v___y_1947_ = v___y_1984_;
v___y_1948_ = v___y_1985_;
v___y_1949_ = v___y_1986_;
v___y_1950_ = v___y_1987_;
v___y_1951_ = v___y_1988_;
v___y_1952_ = v___y_1989_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec(v_goal_1584_);
v_a_2008_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1992_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1992_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
v___jp_2016_:
{
if (lean_obj_tag(v___y_2017_) == 0)
{
lean_dec(v___y_2018_);
v___y_1755_ = v_goal_1584_;
v_progress_1756_ = v_progress_1706_;
v___y_1757_ = v___y_1585_;
v___y_1758_ = v___y_1586_;
v___y_1759_ = v___y_1587_;
v___y_1760_ = v___y_1588_;
v___y_1761_ = v___y_1589_;
v___y_1762_ = v___y_1590_;
v___y_1763_ = v___y_1591_;
v___y_1764_ = v___y_1592_;
v___y_1765_ = v___y_1593_;
v___y_1766_ = v___y_1594_;
v___y_1767_ = v___y_1595_;
goto v___jp_1754_;
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_val_2019_ = lean_ctor_get(v___y_2017_, 0);
v___x_2020_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21);
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22));
lean_inc(v_val_2019_);
v___x_2022_ = l_Lean_Meta_Sym_isDefEqS(v_val_2019_, v___x_2020_, v_progress_1705_, v_progress_1705_, v___x_2021_, v___x_2021_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2024_ == 0)
{
v___y_1976_ = v___y_2017_;
v___y_1977_ = v___y_2018_;
v_pureHNonTrue_1978_ = v_progress_1705_;
v___y_1979_ = v___y_1585_;
v___y_1980_ = v___y_1586_;
v___y_1981_ = v___y_1587_;
v___y_1982_ = v___y_1588_;
v___y_1983_ = v___y_1589_;
v___y_1984_ = v___y_1590_;
v___y_1985_ = v___y_1591_;
v___y_1986_ = v___y_1592_;
v___y_1987_ = v___y_1593_;
v___y_1988_ = v___y_1594_;
v___y_1989_ = v___y_1595_;
goto v___jp_1975_;
}
else
{
lean_dec_ref_known(v___y_2017_, 1);
v___y_1879_ = v___y_2018_;
v_progress_1880_ = v_progress_1706_;
v_goal_1881_ = v_goal_1584_;
v___y_1882_ = v___y_1585_;
v___y_1883_ = v___y_1586_;
v___y_1884_ = v___y_1587_;
v___y_1885_ = v___y_1588_;
v___y_1886_ = v___y_1589_;
v___y_1887_ = v___y_1590_;
v___y_1888_ = v___y_1591_;
v___y_1889_ = v___y_1592_;
v___y_1890_ = v___y_1593_;
v___y_1891_ = v___y_1594_;
v___y_1892_ = v___y_1595_;
goto v___jp_1878_;
}
}
else
{
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2025_; uint8_t v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2026_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
v___y_1976_ = v___y_2017_;
v___y_1977_ = v___y_2018_;
v_pureHNonTrue_1978_ = v___x_2026_;
v___y_1979_ = v___y_1585_;
v___y_1980_ = v___y_1586_;
v___y_1981_ = v___y_1587_;
v___y_1982_ = v___y_1588_;
v___y_1983_ = v___y_1589_;
v___y_1984_ = v___y_1590_;
v___y_1985_ = v___y_1591_;
v___y_1986_ = v___y_1592_;
v___y_1987_ = v___y_1593_;
v___y_1988_ = v___y_1594_;
v___y_1989_ = v___y_1595_;
goto v___jp_1975_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref_known(v___y_2017_, 1);
lean_dec(v___y_2018_);
lean_dec(v_goal_1584_);
v_a_2027_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2022_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
v___jp_2035_:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_unsigned_to_nat(2u);
v___x_2038_ = l_Lean_Expr_isAppOfArity(v_arg_1697_, v___x_1753_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec_ref(v_arg_1697_);
v___x_2039_ = lean_box(0);
v___y_2017_ = v___y_2036_;
v___y_2018_ = v___x_2039_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = l_Lean_Expr_appArg_x21(v_arg_1697_);
lean_dec_ref(v_arg_1697_);
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
v___y_2017_ = v___y_2036_;
v___y_2018_ = v___x_2041_;
goto v___jp_2016_;
}
}
}
}
}
}
v___jp_1690_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_goal_1584_);
v_a_2048_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1685_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1685_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
v___jp_1597_:
{
if (v_progress_1598_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_goal_1599_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_goal_1599_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
v___jp_1604_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
lean_inc(v_goal_1607_);
lean_inc_ref(v_downPureIntroRule_1609_);
v___x_1621_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_downPureIntroRule_1609_, v_goal_1607_, v___x_1620_, v___y_1608_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
if (lean_obj_tag(v_a_1622_) == 1)
{
lean_object* v_mvarIds_1623_; 
v_mvarIds_1623_ = lean_ctor_get(v_a_1622_, 0);
lean_inc(v_mvarIds_1623_);
lean_dec_ref_known(v_a_1622_, 1);
if (lean_obj_tag(v_mvarIds_1623_) == 1)
{
lean_object* v_tail_1624_; 
v_tail_1624_ = lean_ctor_get(v_mvarIds_1623_, 1);
if (lean_obj_tag(v_tail_1624_) == 0)
{
lean_object* v_head_1625_; 
lean_dec(v_goal_1607_);
v_head_1625_ = lean_ctor_get(v_mvarIds_1623_, 0);
lean_inc(v_head_1625_);
lean_dec_ref_known(v_mvarIds_1623_, 2);
v_progress_1598_ = v___y_1605_;
v_goal_1599_ = v_head_1625_;
goto v___jp_1597_;
}
else
{
lean_dec_ref_known(v_mvarIds_1623_, 2);
v_progress_1598_ = v_progress_1606_;
v_goal_1599_ = v_goal_1607_;
goto v___jp_1597_;
}
}
else
{
lean_dec(v_mvarIds_1623_);
v_progress_1598_ = v_progress_1606_;
v_goal_1599_ = v_goal_1607_;
goto v___jp_1597_;
}
}
else
{
lean_dec(v_a_1622_);
v_progress_1598_ = v_progress_1606_;
v_goal_1599_ = v_goal_1607_;
goto v___jp_1597_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_goal_1607_);
v_a_1626_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1621_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1621_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
v___jp_1634_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_box(0);
lean_inc(v_goal_1637_);
lean_inc_ref(v_pureIntroRule_1640_);
v___x_1652_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_pureIntroRule_1640_, v_goal_1637_, v___x_1651_, v___y_1638_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_object* v_mvarIds_1654_; 
v_mvarIds_1654_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_mvarIds_1654_);
lean_dec_ref_known(v_a_1653_, 1);
if (lean_obj_tag(v_mvarIds_1654_) == 1)
{
lean_object* v_tail_1655_; 
v_tail_1655_ = lean_ctor_get(v_mvarIds_1654_, 1);
if (lean_obj_tag(v_tail_1655_) == 0)
{
lean_object* v_head_1656_; 
lean_dec(v_goal_1637_);
v_head_1656_ = lean_ctor_get(v_mvarIds_1654_, 0);
lean_inc(v_head_1656_);
lean_dec_ref_known(v_mvarIds_1654_, 2);
v___y_1605_ = v___y_1635_;
v_progress_1606_ = v___y_1635_;
v_goal_1607_ = v_head_1656_;
v___y_1608_ = v___y_1638_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___y_1644_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1649_;
v___y_1619_ = v___y_1650_;
goto v___jp_1604_;
}
else
{
lean_dec_ref_known(v_mvarIds_1654_, 2);
v___y_1605_ = v___y_1635_;
v_progress_1606_ = v_progress_1636_;
v_goal_1607_ = v_goal_1637_;
v___y_1608_ = v___y_1638_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___y_1644_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1649_;
v___y_1619_ = v___y_1650_;
goto v___jp_1604_;
}
}
else
{
lean_dec(v_mvarIds_1654_);
v___y_1605_ = v___y_1635_;
v_progress_1606_ = v_progress_1636_;
v_goal_1607_ = v_goal_1637_;
v___y_1608_ = v___y_1638_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___y_1644_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1649_;
v___y_1619_ = v___y_1650_;
goto v___jp_1604_;
}
}
else
{
lean_dec(v_a_1653_);
v___y_1605_ = v___y_1635_;
v_progress_1606_ = v_progress_1636_;
v_goal_1607_ = v_goal_1637_;
v___y_1608_ = v___y_1638_;
v_downPureIntroRule_1609_ = v_downPureIntroRule_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___y_1644_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1649_;
v___y_1619_ = v___y_1650_;
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_goal_1637_);
v_a_1657_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1652_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1652_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
v___jp_1665_:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_MVarId_getType(v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
v___x_1674_ = l_Lean_MessageData_ofExpr(v_a_1672_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_1675_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1676_;
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1671_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1671_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed(lean_object* v_goal_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(v_goal_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(lean_object* v_goal_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___f_2083_; lean_object* v___x_2084_; 
lean_inc(v_goal_2070_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2083_, 0, v_goal_2070_);
v___x_2084_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_2070_, v___f_2083_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___boxed(lean_object* v_goal_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(v_goal_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(uint8_t v_progress_2099_, lean_object* v_inst_2100_, lean_object* v_a_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_2099_, v_a_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___boxed(lean_object* v_progress_2115_, lean_object* v_inst_2116_, lean_object* v_a_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_progress_boxed_2130_; lean_object* v_res_2131_; 
v_progress_boxed_2130_ = lean_unbox(v_progress_2115_);
v_res_2131_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(v_progress_boxed_2130_, v_inst_2116_, v_a_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2131_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
}
#ifdef __cplusplus
}
#endif
