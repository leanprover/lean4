// Lean compiler output
// Module: Lean.Meta.Match.AltTelescopes
// Imports: public import Lean.Meta.Match.MatcherInfo import Lean.Meta.Match.NamedPatterns import Lean.Meta.MatchUtil import Lean.Meta.AppBuilder import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_unfoldNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_withReplaceFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withReplaceFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expecting "};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = " parameters, but found type"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Meta.Match.AltTelescopes.0.Lean.Meta.Match.forallAltVarsTelescope.go"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.Match.AltTelescopes"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Match.forallAltVarsTelescope"};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: altInfo.numOverlaps = 0\n  "};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2;
static const lean_array_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8;
static const lean_array_object l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected match alternative type"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = " equalities, but found type"};
static const lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(lean_object* v_h_1_, lean_object* v_e_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2_);
if (lean_obj_tag(v___x_3_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_val_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v___x_3_, 1);
v___x_5_ = l_Lean_Expr_appArg_x21(v_val_4_);
lean_dec(v_val_4_);
v___x_6_ = lean_expr_eqv(v___x_5_, v_h_1_);
lean_dec_ref(v___x_5_);
return v___x_6_;
}
else
{
uint8_t v___x_7_; 
lean_dec(v___x_3_);
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(v_h_1_, v_e_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed(lean_object* v_h_9_, lean_object* v_e_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(v_h_9_, v_e_10_);
lean_dec_ref(v_e_10_);
lean_dec_ref(v_h_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(lean_object* v_type_13_, lean_object* v_h_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; 
v___f_15_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed), 2, 1);
lean_closure_set(v___f_15_, 0, v_h_14_);
v___x_16_ = lean_find_expr(v___f_15_, v_type_13_);
lean_dec_ref(v___f_15_);
if (lean_obj_tag(v___x_16_) == 0)
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = 1;
return v___x_18_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_13_ = stack[0].m_obj;
lean_object* v_h_14_ = stack[1].m_obj;
uint8_t v_res_19_;
v_res_19_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v_type_13_, v_h_14_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___boxed(lean_object* v_type_20_, lean_object* v_h_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v_type_20_, v_h_21_);
lean_dec_ref(v_type_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(lean_object* v_msg_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_2005__overap_32_; lean_object* v___x_33_; 
v___f_31_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_2005__overap_32_ = lean_panic_fn_borrowed(v___f_31_, v_msg_25_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
v___x_33_ = lean_apply_5(v___x_2005__overap_32_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_25_ = stack[0].m_obj;
lean_object* v___y_26_ = stack[1].m_obj;
lean_object* v___y_27_ = stack[2].m_obj;
lean_object* v___y_28_ = stack[3].m_obj;
lean_object* v___y_29_ = stack[4].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v_msg_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___boxed(lean_object* v_msg_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v_msg_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(lean_object* v_xs_42_, lean_object* v_v_43_, lean_object* v_i_44_){
_start:
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_array_get_size(v_xs_42_);
v___x_46_ = lean_nat_dec_lt(v_i_44_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec(v_i_44_);
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_array_fget_borrowed(v_xs_42_, v_i_44_);
v___x_49_ = lean_expr_eqv(v___x_48_, v_v_43_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_i_44_, v___x_50_);
lean_dec(v_i_44_);
v_i_44_ = v___x_51_;
goto _start;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_i_44_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2___boxed(lean_object* v_xs_54_, lean_object* v_v_55_, lean_object* v_i_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_54_, v_v_55_, v_i_56_);
lean_dec_ref(v_v_55_);
lean_dec_ref(v_xs_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(lean_object* v_xs_58_, lean_object* v_v_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_58_, v_v_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1___boxed(lean_object* v_xs_62_, lean_object* v_v_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_62_, v_v_63_);
lean_dec_ref(v_v_63_);
lean_dec_ref(v_xs_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(lean_object* v_xs_65_, lean_object* v_v_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_65_, v_v_66_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_val_69_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_67_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v___x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_val_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2___boxed(lean_object* v_xs_77_, lean_object* v_v_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_xs_77_, v_v_78_);
lean_dec_ref(v_v_78_);
lean_dec_ref(v_xs_77_);
return v_res_79_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(lean_object* v_msgData_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; lean_object* v_env_87_; uint8_t v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_toCold_91_; lean_object* v_mctx_92_; lean_object* v_lctx_93_; lean_object* v_options_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_86_ = lean_st_ref_get(v___y_84_);
v_env_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_env_87_);
lean_dec(v___x_86_);
v___x_88_ = 0;
v_env_89_ = l_Lean_Environment_setRecordingDeps(v_env_87_, v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_82_);
v_toCold_91_ = lean_ctor_get(v___y_83_, 0);
v_mctx_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_92_);
lean_dec(v___x_90_);
v_lctx_93_ = lean_ctor_get(v___y_81_, 2);
v_options_94_ = lean_ctor_get(v_toCold_91_, 2);
lean_inc_ref(v_options_94_);
lean_inc_ref(v_lctx_93_);
v___x_95_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_95_, 0, v_env_89_);
lean_ctor_set(v___x_95_, 1, v_mctx_92_);
lean_ctor_set(v___x_95_, 2, v_lctx_93_);
lean_ctor_set(v___x_95_, 3, v_options_94_);
v___x_96_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_msgData_80_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_80_ = stack[0].m_obj;
lean_object* v___y_81_ = stack[1].m_obj;
lean_object* v___y_82_ = stack[2].m_obj;
lean_object* v___y_83_ = stack[3].m_obj;
lean_object* v___y_84_ = stack[4].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_ref_112_; lean_object* v___x_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_ref_112_ = lean_ctor_get(v___y_109_, 2);
v___x_113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msg_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc(v_ref_112_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_ref_112_);
lean_ctor_set(v___x_118_, 1, v_a_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_106_ = stack[0].m_obj;
lean_object* v___y_107_ = stack[1].m_obj;
lean_object* v___y_108_ = stack[2].m_obj;
lean_object* v___y_109_ = stack[3].m_obj;
lean_object* v___y_110_ = stack[4].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(lean_object* v_k_131_, lean_object* v_b_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_138_ = lean_apply_6(v_k_131_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_131_ = stack[0].m_obj;
lean_object* v_b_132_ = stack[1].m_obj;
lean_object* v___y_133_ = stack[2].m_obj;
lean_object* v___y_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v___y_136_ = stack[5].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_131_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_140_, lean_object* v_b_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_140_, v_b_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(lean_object* v_name_148_, uint8_t v_bi_149_, lean_object* v_type_150_, lean_object* v_k_151_, uint8_t v_kind_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; 
v___f_158_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_158_, 0, v_k_151_);
v___x_159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_148_, v_bi_149_, v_type_150_, v___f_158_, v_kind_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_159_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_148_ = stack[0].m_obj;
uint8_t v_bi_149_ = stack[1].m_num;
lean_object* v_type_150_ = stack[2].m_obj;
lean_object* v_k_151_ = stack[3].m_obj;
uint8_t v_kind_152_ = stack[4].m_num;
lean_object* v___y_153_ = stack[5].m_obj;
lean_object* v___y_154_ = stack[6].m_obj;
lean_object* v___y_155_ = stack[7].m_obj;
lean_object* v___y_156_ = stack[8].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_148_, v_bi_149_, v_type_150_, v_k_151_, v_kind_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(lean_object* v_name_177_, lean_object* v_bi_178_, lean_object* v_type_179_, lean_object* v_k_180_, lean_object* v_kind_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v_bi_boxed_187_; uint8_t v_kind_boxed_188_; lean_object* v_res_189_; 
v_bi_boxed_187_ = lean_unbox(v_bi_178_);
v_kind_boxed_188_ = lean_unbox(v_kind_181_);
v_res_189_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_177_, v_bi_boxed_187_, v_type_179_, v_k_180_, v_kind_boxed_188_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_189_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(lean_object* v_name_190_, lean_object* v_type_191_, lean_object* v_k_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = 0;
v___x_199_ = 0;
v___x_200_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_190_, v___x_198_, v_type_191_, v_k_192_, v___x_199_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
return v___x_200_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_190_ = stack[0].m_obj;
lean_object* v_type_191_ = stack[1].m_obj;
lean_object* v_k_192_ = stack[2].m_obj;
lean_object* v___y_193_ = stack[3].m_obj;
lean_object* v___y_194_ = stack[4].m_obj;
lean_object* v___y_195_ = stack[5].m_obj;
lean_object* v___y_196_ = stack[6].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_190_, v_type_191_, v_k_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(lean_object* v_name_202_, lean_object* v_type_203_, lean_object* v_k_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_202_, v_type_203_, v_k_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_210_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(lean_object* v_fst_211_, lean_object* v_snd_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_snd_212_);
return v_bs_215_;
}
else
{
lean_object* v_v_217_; lean_object* v___x_218_; lean_object* v_bs_x27_219_; lean_object* v___y_221_; uint8_t v___x_226_; 
v_v_217_ = lean_array_uget(v_bs_215_, v_i_214_);
v___x_218_ = lean_unsigned_to_nat(0u);
v_bs_x27_219_ = lean_array_uset(v_bs_215_, v_i_214_, v___x_218_);
v___x_226_ = lean_expr_eqv(v_v_217_, v_fst_211_);
if (v___x_226_ == 0)
{
v___y_221_ = v_v_217_;
goto v___jp_220_;
}
else
{
lean_dec(v_v_217_);
lean_inc_ref(v_snd_212_);
v___y_221_ = v_snd_212_;
goto v___jp_220_;
}
v___jp_220_:
{
size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; 
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_214_, v___x_222_);
v___x_224_ = lean_array_uset(v_bs_x27_219_, v_i_214_, v___y_221_);
v_i_214_ = v___x_223_;
v_bs_215_ = v___x_224_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_211_ = stack[0].m_obj;
lean_object* v_snd_212_ = stack[1].m_obj;
size_t v_sz_213_ = stack[2].m_num;
size_t v_i_214_ = stack[3].m_num;
lean_object* v_bs_215_ = stack[4].m_obj;
lean_object* v_res_227_;
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_211_, v_snd_212_, v_sz_213_, v_i_214_, v_bs_215_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(lean_object* v_fst_228_, lean_object* v_snd_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_bs_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_228_, v_snd_229_, v_sz_boxed_233_, v_i_boxed_234_, v_bs_232_);
lean_dec_ref(v_fst_228_);
return v_res_235_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(lean_object* v_a_236_, lean_object* v_as_237_, size_t v_i_238_, size_t v_stop_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_eq(v_i_238_, v_stop_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_array_uget_borrowed(v_as_237_, v_i_238_);
v___x_242_ = lean_expr_eqv(v_a_236_, v___x_241_);
if (v___x_242_ == 0)
{
size_t v___x_243_; size_t v___x_244_; 
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_add(v_i_238_, v___x_243_);
v_i_238_ = v___x_244_;
goto _start;
}
else
{
return v___x_242_;
}
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_236_ = stack[0].m_obj;
lean_object* v_as_237_ = stack[1].m_obj;
size_t v_i_238_ = stack[2].m_num;
size_t v_stop_239_ = stack[3].m_num;
uint8_t v_res_247_;
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_236_, v_as_237_, v_i_238_, v_stop_239_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(lean_object* v_a_248_, lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_stop_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_stop_boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_stop_boxed_253_ = lean_unbox_usize(v_stop_251_);
lean_dec(v_stop_251_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_248_, v_as_249_, v_i_boxed_252_, v_stop_boxed_253_);
lean_dec_ref(v_as_249_);
lean_dec_ref(v_a_248_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(lean_object* v_as_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_array_get_size(v_as_256_);
v___x_260_ = lean_nat_dec_lt(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
return v___x_260_;
}
else
{
if (v___x_260_ == 0)
{
return v___x_260_;
}
else
{
size_t v___x_261_; size_t v___x_262_; uint8_t v___x_263_; 
v___x_261_ = ((size_t)0ULL);
v___x_262_ = lean_usize_of_nat(v___x_259_);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_257_, v_as_256_, v___x_261_, v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_256_ = stack[0].m_obj;
lean_object* v_a_257_ = stack[1].m_obj;
uint8_t v_res_264_;
v_res_264_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_256_, v_a_257_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(lean_object* v_as_265_, lean_object* v_a_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_265_, v_a_266_);
lean_dec_ref(v_a_266_);
lean_dec_ref(v_as_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(lean_object* v_altType_275_, lean_object* v_altInfo_276_, lean_object* v_k_277_, lean_object* v_ys_278_, lean_object* v_args_279_, lean_object* v_mask_280_, lean_object* v_i_281_, lean_object* v_type_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_275_, v_altInfo_276_, v_k_277_, v_ys_278_, v_args_279_, v_mask_280_, v_i_281_, v_type_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
return v_res_288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_293_ = lean_unsigned_to_nat(47u);
v___x_294_ = lean_unsigned_to_nat(68u);
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_297_ = l_mkPanicMessageWithDecl(v___x_296_, v___x_295_, v___x_294_, v___x_293_, v___x_292_);
return v___x_297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_299_ = lean_unsigned_to_nat(48u);
v___x_300_ = lean_unsigned_to_nat(66u);
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_302_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_303_ = l_mkPanicMessageWithDecl(v___x_302_, v___x_301_, v___x_300_, v___x_299_, v___x_298_);
return v___x_303_;
}
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object* v_body_304_, lean_object* v_ys_305_, lean_object* v_args_306_, lean_object* v_mask_307_, uint8_t v___x_308_, lean_object* v_i_309_, lean_object* v_altType_310_, lean_object* v_altInfo_311_, lean_object* v_k_312_, lean_object* v_a_313_, lean_object* v_y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_329_; 
v___x_320_ = lean_expr_instantiate1(v_body_304_, v_y_314_);
v___x_329_ = l_Lean_Meta_matchEq_x3f(v_a_313_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
if (lean_obj_tag(v_a_330_) == 1)
{
lean_object* v_val_331_; lean_object* v_snd_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; uint8_t v___y_336_; uint8_t v___x_391_; 
v_val_331_ = lean_ctor_get(v_a_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v_a_330_, 1);
v_snd_332_ = lean_ctor_get(v_val_331_, 1);
lean_inc(v_snd_332_);
lean_dec(v_val_331_);
v_fst_333_ = lean_ctor_get(v_snd_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_snd_332_, 1);
lean_inc(v_snd_334_);
lean_dec(v_snd_332_);
v___x_391_ = l_Lean_Expr_isFVar(v_fst_333_);
if (v___x_391_ == 0)
{
v___y_336_ = v___x_391_;
goto v___jp_335_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_305_, v_fst_333_);
v___y_336_ = v___x_392_;
goto v___jp_335_;
}
v___jp_335_:
{
if (v___y_336_ == 0)
{
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
goto v___jp_321_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_306_, v_fst_333_);
if (v___x_337_ == 0)
{
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
goto v___jp_321_;
}
else
{
uint8_t v___x_338_; 
lean_inc_ref(v_y_314_);
v___x_338_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_320_, v_y_314_);
if (v___x_338_ == 0)
{
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
goto v___jp_321_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_305_, v_fst_333_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_341_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_306_, v_fst_333_);
if (lean_obj_tag(v___x_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; size_t v_sz_347_; size_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_val_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_val_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = l_Array_eraseIdx___redArg(v_ys_305_, v_val_340_);
v___x_344_ = 0;
v___x_345_ = lean_box(v___x_344_);
v___x_346_ = lean_array_set(v_mask_307_, v_val_342_, v___x_345_);
lean_dec(v_val_342_);
v_sz_347_ = lean_array_size(v_args_306_);
v___x_348_ = ((size_t)0ULL);
lean_inc_n(v_snd_334_, 2);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_333_, v_snd_334_, v_sz_347_, v___x_348_, v_args_306_);
v___x_350_ = l_Lean_Meta_mkEqRefl(v_snd_334_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_n(v_a_351_, 2);
lean_dec_ref_known(v___x_350_, 1);
lean_inc(v_fst_333_);
v___x_352_ = l_Lean_Expr_replaceFVar(v___x_320_, v_fst_333_, v_snd_334_);
lean_dec_ref(v___x_320_);
v___x_353_ = l_Lean_Expr_fvarId_x21(v_fst_333_);
lean_dec(v_fst_333_);
v___x_354_ = l_Lean_Expr_fvarId_x21(v_y_314_);
lean_dec_ref(v_y_314_);
v___x_355_ = lean_array_push(v___x_349_, v_a_351_);
v___x_356_ = lean_box(v___x_344_);
v___x_357_ = lean_array_push(v___x_346_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_i_309_, v___x_358_);
v___x_360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed), 13, 8);
lean_closure_set(v___x_360_, 0, v_altType_310_);
lean_closure_set(v___x_360_, 1, v_altInfo_311_);
lean_closure_set(v___x_360_, 2, v_k_312_);
lean_closure_set(v___x_360_, 3, v___x_343_);
lean_closure_set(v___x_360_, 4, v___x_355_);
lean_closure_set(v___x_360_, 5, v___x_357_);
lean_closure_set(v___x_360_, 6, v___x_359_);
lean_closure_set(v___x_360_, 7, v___x_352_);
v___x_361_ = lean_alloc_closure((void*)(l_Lean_Meta_withReplaceFVarId___boxed), 9, 4);
lean_closure_set(v___x_361_, 0, lean_box(0));
lean_closure_set(v___x_361_, 1, v___x_354_);
lean_closure_set(v___x_361_, 2, v_a_351_);
lean_closure_set(v___x_361_, 3, v___x_360_);
v___x_362_ = l_Lean_Meta_withReplaceFVarId___redArg(v___x_353_, v_snd_334_, v___x_361_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
return v___x_362_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
lean_dec_ref(v___x_320_);
lean_dec_ref(v_y_314_);
lean_dec_ref(v_k_312_);
lean_dec_ref(v_altInfo_311_);
lean_dec_ref(v_altType_310_);
v_a_363_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_350_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_350_);
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
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_341_);
lean_dec(v_val_340_);
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
v___x_372_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_371_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref_known(v___x_372_, 1);
goto v___jp_321_;
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_y_314_);
lean_dec_ref(v_k_312_);
lean_dec_ref(v_altInfo_311_);
lean_dec_ref(v_altType_310_);
lean_dec_ref(v_mask_307_);
lean_dec_ref(v_args_306_);
lean_dec_ref(v_ys_305_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v___x_339_);
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
v___x_382_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_381_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_dec_ref_known(v___x_382_, 1);
goto v___jp_321_;
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_y_314_);
lean_dec_ref(v_k_312_);
lean_dec_ref(v_altInfo_311_);
lean_dec_ref(v_altType_310_);
lean_dec_ref(v_mask_307_);
lean_dec_ref(v_args_306_);
lean_dec_ref(v_ys_305_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
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
lean_dec(v_a_330_);
goto v___jp_321_;
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_y_314_);
lean_dec_ref(v_k_312_);
lean_dec_ref(v_altInfo_311_);
lean_dec_ref(v_altType_310_);
lean_dec_ref(v_mask_307_);
lean_dec_ref(v_args_306_);
lean_dec_ref(v_ys_305_);
v_a_393_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_329_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_329_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_inc_ref(v_y_314_);
v___x_322_ = lean_array_push(v_ys_305_, v_y_314_);
v___x_323_ = lean_array_push(v_args_306_, v_y_314_);
v___x_324_ = lean_box(v___x_308_);
v___x_325_ = lean_array_push(v_mask_307_, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v_i_309_, v___x_326_);
v___x_328_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_310_, v_altInfo_311_, v_k_312_, v___x_322_, v___x_323_, v___x_325_, v___x_327_, v___x_320_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
return v___x_328_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_304_ = stack[0].m_obj;
lean_object* v_ys_305_ = stack[1].m_obj;
lean_object* v_args_306_ = stack[2].m_obj;
lean_object* v_mask_307_ = stack[3].m_obj;
uint8_t v___x_308_ = stack[4].m_num;
lean_object* v_i_309_ = stack[5].m_obj;
lean_object* v_altType_310_ = stack[6].m_obj;
lean_object* v_altInfo_311_ = stack[7].m_obj;
lean_object* v_k_312_ = stack[8].m_obj;
lean_object* v_a_313_ = stack[9].m_obj;
lean_object* v_y_314_ = stack[10].m_obj;
lean_object* v___y_315_ = stack[11].m_obj;
lean_object* v___y_316_ = stack[12].m_obj;
lean_object* v___y_317_ = stack[13].m_obj;
lean_object* v___y_318_ = stack[14].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_body_304_, v_ys_305_, v_args_306_, v_mask_307_, v___x_308_, v_i_309_, v_altType_310_, v_altInfo_311_, v_k_312_, v_a_313_, v_y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object* v_body_402_, lean_object* v_ys_403_, lean_object* v_args_404_, lean_object* v_mask_405_, lean_object* v___x_406_, lean_object* v_i_407_, lean_object* v_altType_408_, lean_object* v_altInfo_409_, lean_object* v_k_410_, lean_object* v_a_411_, lean_object* v_y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
uint8_t v___x_4218__boxed_418_; lean_object* v_res_419_; 
v___x_4218__boxed_418_ = lean_unbox(v___x_406_);
v_res_419_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_body_402_, v_ys_403_, v_args_404_, v_mask_405_, v___x_4218__boxed_418_, v_i_407_, v_altType_408_, v_altInfo_409_, v_k_410_, v_a_411_, v_y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_i_407_);
lean_dec_ref(v_body_402_);
return v_res_419_;
}
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(lean_object* v_altType_420_, lean_object* v_altInfo_421_, lean_object* v_k_422_, lean_object* v_ys_423_, lean_object* v_args_424_, lean_object* v_mask_425_, lean_object* v_i_426_, lean_object* v_type_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_whnfForall(v_type_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_numFields_435_; uint8_t v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v_numFields_435_ = lean_ctor_get(v_altInfo_421_, 0);
v___x_436_ = lean_nat_dec_lt(v_i_426_, v_numFields_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_dec(v_i_426_);
lean_dec_ref(v_altInfo_421_);
lean_dec_ref(v_altType_420_);
v___x_437_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_434_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
lean_inc(v_a_431_);
lean_inc_ref(v_a_430_);
lean_inc(v_a_429_);
lean_inc_ref(v_a_428_);
v___x_439_ = lean_apply_9(v_k_422_, v_ys_423_, v_args_424_, v_mask_425_, v_a_438_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, lean_box(0));
return v___x_439_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_mask_425_);
lean_dec_ref(v_args_424_);
lean_dec_ref(v_ys_423_);
lean_dec_ref(v_k_422_);
v_a_440_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_437_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
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
else
{
if (lean_obj_tag(v_a_434_) == 7)
{
lean_object* v_binderName_448_; lean_object* v_binderType_449_; lean_object* v_body_450_; lean_object* v___x_451_; 
v_binderName_448_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_binderName_448_);
v_binderType_449_ = lean_ctor_get(v_a_434_, 1);
lean_inc_ref(v_binderType_449_);
v_body_450_ = lean_ctor_get(v_a_434_, 2);
lean_inc_ref(v_body_450_);
lean_dec_ref_known(v_a_434_, 3);
v___x_451_ = l_Lean_Meta_Match_unfoldNamedPattern(v_binderType_449_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc_n(v_a_452_, 2);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = lean_box(v___x_436_);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_454_, 0, v_body_450_);
lean_closure_set(v___f_454_, 1, v_ys_423_);
lean_closure_set(v___f_454_, 2, v_args_424_);
lean_closure_set(v___f_454_, 3, v_mask_425_);
lean_closure_set(v___f_454_, 4, v___x_453_);
lean_closure_set(v___f_454_, 5, v_i_426_);
lean_closure_set(v___f_454_, 6, v_altType_420_);
lean_closure_set(v___f_454_, 7, v_altInfo_421_);
lean_closure_set(v___f_454_, 8, v_k_422_);
lean_closure_set(v___f_454_, 9, v_a_452_);
v___x_455_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_448_, v_a_452_, v___f_454_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_body_450_);
lean_dec(v_binderName_448_);
lean_dec(v_i_426_);
lean_dec_ref(v_mask_425_);
lean_dec_ref(v_args_424_);
lean_dec_ref(v_ys_423_);
lean_dec_ref(v_k_422_);
lean_dec_ref(v_altInfo_421_);
lean_dec_ref(v_altType_420_);
v_a_456_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_451_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_451_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc(v_numFields_435_);
lean_dec(v_a_434_);
lean_dec(v_i_426_);
lean_dec_ref(v_mask_425_);
lean_dec_ref(v_args_424_);
lean_dec_ref(v_ys_423_);
lean_dec_ref(v_k_422_);
lean_dec_ref(v_altInfo_421_);
v___x_464_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_465_ = l_Nat_reprFast(v_numFields_435_);
v___x_466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = l_Lean_MessageData_ofFormat(v___x_466_);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_indentExpr(v_altType_420_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_472_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_473_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_i_426_);
lean_dec_ref(v_mask_425_);
lean_dec_ref(v_args_424_);
lean_dec_ref(v_ys_423_);
lean_dec_ref(v_k_422_);
lean_dec_ref(v_altInfo_421_);
lean_dec_ref(v_altType_420_);
v_a_474_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_433_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_433_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_420_ = stack[0].m_obj;
lean_object* v_altInfo_421_ = stack[1].m_obj;
lean_object* v_k_422_ = stack[2].m_obj;
lean_object* v_ys_423_ = stack[3].m_obj;
lean_object* v_args_424_ = stack[4].m_obj;
lean_object* v_mask_425_ = stack[5].m_obj;
lean_object* v_i_426_ = stack[6].m_obj;
lean_object* v_type_427_ = stack[7].m_obj;
lean_object* v_a_428_ = stack[8].m_obj;
lean_object* v_a_429_ = stack[9].m_obj;
lean_object* v_a_430_ = stack[10].m_obj;
lean_object* v_a_431_ = stack[11].m_obj;
lean_object* v_res_482_;
v_res_482_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_420_, v_altInfo_421_, v_k_422_, v_ys_423_, v_args_424_, v_mask_425_, v_i_426_, v_type_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
stack->m_obj
 = v_res_482_;
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_object* v_00_u03b1_483_, lean_object* v_altType_484_, lean_object* v_altInfo_485_, lean_object* v_k_486_, lean_object* v_ys_487_, lean_object* v_args_488_, lean_object* v_mask_489_, lean_object* v_i_490_, lean_object* v_type_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_484_, v_altInfo_485_, v_k_486_, v_ys_487_, v_args_488_, v_mask_489_, v_i_490_, v_type_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_497_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_484_ = stack[1].m_obj;
lean_object* v_altInfo_485_ = stack[2].m_obj;
lean_object* v_k_486_ = stack[3].m_obj;
lean_object* v_ys_487_ = stack[4].m_obj;
lean_object* v_args_488_ = stack[5].m_obj;
lean_object* v_mask_489_ = stack[6].m_obj;
lean_object* v_i_490_ = stack[7].m_obj;
lean_object* v_type_491_ = stack[8].m_obj;
lean_object* v_a_492_ = stack[9].m_obj;
lean_object* v_a_493_ = stack[10].m_obj;
lean_object* v_a_494_ = stack[11].m_obj;
lean_object* v_a_495_ = stack[12].m_obj;
lean_object* v_res_498_;
v_res_498_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_box(0), v_altType_484_, v_altInfo_485_, v_k_486_, v_ys_487_, v_args_488_, v_mask_489_, v_i_490_, v_type_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(lean_object* v_00_u03b1_499_, lean_object* v_altType_500_, lean_object* v_altInfo_501_, lean_object* v_k_502_, lean_object* v_ys_503_, lean_object* v_args_504_, lean_object* v_mask_505_, lean_object* v_i_506_, lean_object* v_type_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(v_00_u03b1_499_, v_altType_500_, v_altInfo_501_, v_k_502_, v_ys_503_, v_args_504_, v_mask_505_, v_i_506_, v_type_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_513_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_object* v_00_u03b1_514_, lean_object* v_name_515_, uint8_t v_bi_516_, lean_object* v_type_517_, lean_object* v_k_518_, uint8_t v_kind_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_515_, v_bi_516_, v_type_517_, v_k_518_, v_kind_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_515_ = stack[1].m_obj;
uint8_t v_bi_516_ = stack[2].m_num;
lean_object* v_type_517_ = stack[3].m_obj;
lean_object* v_k_518_ = stack[4].m_obj;
uint8_t v_kind_519_ = stack[5].m_num;
lean_object* v___y_520_ = stack[6].m_obj;
lean_object* v___y_521_ = stack[7].m_obj;
lean_object* v___y_522_ = stack[8].m_obj;
lean_object* v___y_523_ = stack[9].m_obj;
lean_object* v_res_526_;
v_res_526_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_box(0), v_name_515_, v_bi_516_, v_type_517_, v_k_518_, v_kind_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_527_, lean_object* v_name_528_, lean_object* v_bi_529_, lean_object* v_type_530_, lean_object* v_k_531_, lean_object* v_kind_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_bi_boxed_538_; uint8_t v_kind_boxed_539_; lean_object* v_res_540_; 
v_bi_boxed_538_ = lean_unbox(v_bi_529_);
v_kind_boxed_539_ = lean_unbox(v_kind_532_);
v_res_540_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(v_00_u03b1_527_, v_name_528_, v_bi_boxed_538_, v_type_530_, v_k_531_, v_kind_boxed_539_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_540_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_object* v_00_u03b1_541_, lean_object* v_name_542_, lean_object* v_type_543_, lean_object* v_k_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_542_, v_type_543_, v_k_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_542_ = stack[1].m_obj;
lean_object* v_type_543_ = stack[2].m_obj;
lean_object* v_k_544_ = stack[3].m_obj;
lean_object* v___y_545_ = stack[4].m_obj;
lean_object* v___y_546_ = stack[5].m_obj;
lean_object* v___y_547_ = stack[6].m_obj;
lean_object* v___y_548_ = stack[7].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_box(0), v_name_542_, v_type_543_, v_k_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(lean_object* v_00_u03b1_552_, lean_object* v_name_553_, lean_object* v_type_554_, lean_object* v_k_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(v_00_u03b1_552_, v_name_553_, v_type_554_, v_k_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_object* v_00_u03b1_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_563_ = stack[1].m_obj;
lean_object* v___y_564_ = stack[2].m_obj;
lean_object* v___y_565_ = stack[3].m_obj;
lean_object* v___y_566_ = stack[4].m_obj;
lean_object* v___y_567_ = stack[5].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_box(0), v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(lean_object* v_00_u03b1_571_, lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(v_00_u03b1_571_, v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_578_;
}
}
lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___f_585_; lean_object* v___x_403__overap_586_; lean_object* v___x_587_; 
v___f_585_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_403__overap_586_ = lean_panic_fn_borrowed(v___f_585_, v_msg_579_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_587_ = lean_apply_5(v___x_403__overap_586_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, lean_box(0));
return v___x_587_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_579_ = stack[0].m_obj;
lean_object* v___y_580_ = stack[1].m_obj;
lean_object* v___y_581_ = stack[2].m_obj;
lean_object* v___y_582_ = stack[3].m_obj;
lean_object* v___y_583_ = stack[4].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_object* v_00_u03b1_596_, lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
return v___x_603_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_597_ = stack[1].m_obj;
lean_object* v___y_598_ = stack[2].m_obj;
lean_object* v___y_599_ = stack[3].m_obj;
lean_object* v___y_600_ = stack[4].m_obj;
lean_object* v___y_601_ = stack[5].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_box(0), v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(lean_object* v_00_u03b1_605_, lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(v_00_u03b1_605_, v_msg_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1));
v___x_616_ = lean_unsigned_to_nat(2u);
v___x_617_ = lean_unsigned_to_nat(45u);
v___x_618_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0));
v___x_619_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_620_ = l_mkPanicMessageWithDecl(v___x_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_box(0);
v___x_629_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6));
v___x_630_ = l_Lean_mkConst(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
v___x_634_ = lean_array_push(v___x_633_, v___x_631_);
return v___x_634_;
}
}
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object* v_altType_640_, lean_object* v_altInfo_641_, lean_object* v_k_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_numOverlaps_648_; uint8_t v_hasUnitThunk_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_numOverlaps_648_ = lean_ctor_get(v_altInfo_641_, 1);
v_hasUnitThunk_649_ = lean_ctor_get_uint8(v_altInfo_641_, sizeof(void*)*2);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_nat_dec_eq(v_numOverlaps_648_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v_k_642_);
lean_dec_ref(v_altInfo_641_);
lean_dec_ref(v_altType_640_);
v___x_652_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2);
v___x_653_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v___x_652_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
return v___x_653_;
}
else
{
if (v_hasUnitThunk_649_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
lean_inc_ref(v_altType_640_);
v___x_655_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_640_, v_altInfo_641_, v_k_642_, v___x_654_, v___x_654_, v___x_654_, v___x_650_, v_altType_640_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; 
lean_dec_ref(v_altInfo_641_);
v___x_656_ = l_Lean_Meta_whnfForall(v_altType_640_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_657_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8);
v___x_661_ = l_Lean_Meta_instantiateForall(v_a_659_, v___x_660_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_664_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9));
lean_inc(v_a_646_);
lean_inc_ref(v_a_645_);
lean_inc(v_a_644_);
lean_inc_ref(v_a_643_);
v___x_665_ = lean_apply_9(v_k_642_, v___x_663_, v___x_660_, v___x_664_, v_a_662_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, lean_box(0));
return v___x_665_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_k_642_);
v_a_666_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_661_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_661_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_k_642_);
v_a_674_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_658_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_658_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
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
lean_dec_ref(v_k_642_);
v_a_682_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_656_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_656_);
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
}
LEAN_EXPORT void l_Lean_Meta_Match_forallAltVarsTelescope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_640_ = stack[0].m_obj;
lean_object* v_altInfo_641_ = stack[1].m_obj;
lean_object* v_k_642_ = stack[2].m_obj;
lean_object* v_a_643_ = stack[3].m_obj;
lean_object* v_a_644_ = stack[4].m_obj;
lean_object* v_a_645_ = stack[5].m_obj;
lean_object* v_a_646_ = stack[6].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_640_, v_altInfo_641_, v_k_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(lean_object* v_altType_691_, lean_object* v_altInfo_692_, lean_object* v_k_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_691_, v_altInfo_692_, v_k_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_699_;
}
}
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope(lean_object* v_00_u03b1_700_, lean_object* v_altType_701_, lean_object* v_altInfo_702_, lean_object* v_k_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_701_, v_altInfo_702_, v_k_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_709_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_forallAltVarsTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_701_ = stack[1].m_obj;
lean_object* v_altInfo_702_ = stack[2].m_obj;
lean_object* v_k_703_ = stack[3].m_obj;
lean_object* v_a_704_ = stack[4].m_obj;
lean_object* v_a_705_ = stack[5].m_obj;
lean_object* v_a_706_ = stack[6].m_obj;
lean_object* v_a_707_ = stack[7].m_obj;
lean_object* v_res_710_;
v_res_710_ = l_Lean_Meta_Match_forallAltVarsTelescope(lean_box(0), v_altType_701_, v_altInfo_702_, v_k_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___boxed(lean_object* v_00_u03b1_711_, lean_object* v_altType_712_, lean_object* v_altInfo_713_, lean_object* v_k_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Match_forallAltVarsTelescope(v_00_u03b1_711_, v_altType_712_, v_altInfo_713_, v_k_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(lean_object* v_body_721_, lean_object* v_eqs_722_, lean_object* v_args_723_, lean_object* v_arg_724_, lean_object* v_mask_725_, lean_object* v_i_726_, lean_object* v_altType_727_, lean_object* v_numDiscrEqs_728_, lean_object* v_k_729_, lean_object* v_ys_730_, lean_object* v_eq_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_721_, v_eqs_722_, v_args_723_, v_arg_724_, v_mask_725_, v_i_726_, v_altType_727_, v_numDiscrEqs_728_, v_k_729_, v_ys_730_, v_eq_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_i_726_);
lean_dec_ref(v_body_721_);
return v_res_737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(lean_object* v_altType_744_, lean_object* v_numDiscrEqs_745_, lean_object* v_k_746_, lean_object* v_ys_747_, lean_object* v_eqs_748_, lean_object* v_args_749_, lean_object* v_mask_750_, lean_object* v_i_751_, lean_object* v_type_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_whnfForall(v_type_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; uint8_t v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = lean_nat_dec_lt(v_i_751_, v_numDiscrEqs_745_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_i_751_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v___x_761_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_759_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc(v_a_754_);
lean_inc_ref(v_a_753_);
v___x_763_ = lean_apply_10(v_k_746_, v_ys_747_, v_eqs_748_, v_args_749_, v_mask_750_, v_a_762_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, lean_box(0));
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
v_a_764_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_761_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_759_) == 7)
{
lean_object* v_binderName_772_; lean_object* v_binderType_773_; lean_object* v_body_774_; lean_object* v_arg_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___x_783_; 
v_binderName_772_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_binderName_772_);
v_binderType_773_ = lean_ctor_get(v_a_759_, 1);
lean_inc_ref_n(v_binderType_773_, 2);
v_body_774_ = lean_ctor_get(v_a_759_, 2);
lean_inc_ref(v_body_774_);
lean_dec_ref_known(v_a_759_, 3);
v___x_783_ = l_Lean_Meta_matchEq_x3f(v_binderType_773_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
if (lean_obj_tag(v_a_784_) == 1)
{
lean_object* v_val_785_; lean_object* v_snd_786_; lean_object* v_snd_787_; lean_object* v___x_788_; 
v_val_785_ = lean_ctor_get(v_a_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v_a_784_, 1);
v_snd_786_ = lean_ctor_get(v_val_785_, 1);
lean_inc(v_snd_786_);
lean_dec(v_val_785_);
v_snd_787_ = lean_ctor_get(v_snd_786_, 1);
lean_inc(v_snd_787_);
lean_dec(v_snd_786_);
v___x_788_ = l_Lean_Meta_mkEqRefl(v_snd_787_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_arg_776_ = v_a_789_;
v___y_777_ = v_a_753_;
v___y_778_ = v_a_754_;
v___y_779_ = v_a_755_;
v___y_780_ = v_a_756_;
goto v___jp_775_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_body_774_);
lean_dec_ref(v_binderType_773_);
lean_dec(v_binderName_772_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_790_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_798_; 
lean_dec(v_a_784_);
lean_inc_ref(v_binderType_773_);
v___x_798_ = l_Lean_Meta_matchHEq_x3f(v_binderType_773_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
if (lean_obj_tag(v_a_799_) == 1)
{
lean_object* v_val_800_; lean_object* v_snd_801_; lean_object* v_snd_802_; lean_object* v_snd_803_; lean_object* v___x_804_; 
v_val_800_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_a_799_, 1);
v_snd_801_ = lean_ctor_get(v_val_800_, 1);
lean_inc(v_snd_801_);
lean_dec(v_val_800_);
v_snd_802_ = lean_ctor_get(v_snd_801_, 1);
lean_inc(v_snd_802_);
lean_dec(v_snd_801_);
v_snd_803_ = lean_ctor_get(v_snd_802_, 1);
lean_inc(v_snd_803_);
lean_dec(v_snd_802_);
v___x_804_ = l_Lean_Meta_mkHEqRefl(v_snd_803_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v_arg_776_ = v_a_805_;
v___y_777_ = v_a_753_;
v___y_778_ = v_a_754_;
v___y_779_ = v_a_755_;
v___y_780_ = v_a_756_;
goto v___jp_775_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_body_774_);
lean_dec_ref(v_binderType_773_);
lean_dec(v_binderName_772_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_806_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_a_799_);
v___x_814_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
lean_inc_ref(v_altType_744_);
v___x_815_ = l_Lean_indentExpr(v_altType_744_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_816_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v_arg_776_ = v_a_818_;
v___y_777_ = v_a_753_;
v___y_778_ = v_a_754_;
v___y_779_ = v_a_755_;
v___y_780_ = v_a_756_;
goto v___jp_775_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_body_774_);
lean_dec_ref(v_binderType_773_);
lean_dec(v_binderName_772_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_body_774_);
lean_dec_ref(v_binderType_773_);
lean_dec(v_binderName_772_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_827_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_798_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_798_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_body_774_);
lean_dec_ref(v_binderType_773_);
lean_dec(v_binderName_772_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_835_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_783_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_783_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
v___jp_775_:
{
lean_object* v___f_781_; lean_object* v___x_782_; 
v___f_781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_781_, 0, v_body_774_);
lean_closure_set(v___f_781_, 1, v_eqs_748_);
lean_closure_set(v___f_781_, 2, v_args_749_);
lean_closure_set(v___f_781_, 3, v_arg_776_);
lean_closure_set(v___f_781_, 4, v_mask_750_);
lean_closure_set(v___f_781_, 5, v_i_751_);
lean_closure_set(v___f_781_, 6, v_altType_744_);
lean_closure_set(v___f_781_, 7, v_numDiscrEqs_745_);
lean_closure_set(v___f_781_, 8, v_k_746_);
lean_closure_set(v___f_781_, 9, v_ys_747_);
v___x_782_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_772_, v_binderType_773_, v___f_781_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_a_759_);
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_844_ = l_Nat_reprFast(v_numDiscrEqs_745_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = l_Lean_MessageData_ofFormat(v___x_845_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_843_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_indentExpr(v_altType_744_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_851_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
return v___x_852_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_i_751_);
lean_dec_ref(v_mask_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_eqs_748_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_k_746_);
lean_dec(v_numDiscrEqs_745_);
lean_dec_ref(v_altType_744_);
v_a_853_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_758_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_758_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_744_ = stack[0].m_obj;
lean_object* v_numDiscrEqs_745_ = stack[1].m_obj;
lean_object* v_k_746_ = stack[2].m_obj;
lean_object* v_ys_747_ = stack[3].m_obj;
lean_object* v_eqs_748_ = stack[4].m_obj;
lean_object* v_args_749_ = stack[5].m_obj;
lean_object* v_mask_750_ = stack[6].m_obj;
lean_object* v_i_751_ = stack[7].m_obj;
lean_object* v_type_752_ = stack[8].m_obj;
lean_object* v_a_753_ = stack[9].m_obj;
lean_object* v_a_754_ = stack[10].m_obj;
lean_object* v_a_755_ = stack[11].m_obj;
lean_object* v_a_756_ = stack[12].m_obj;
lean_object* v_res_861_;
v_res_861_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_744_, v_numDiscrEqs_745_, v_k_746_, v_ys_747_, v_eqs_748_, v_args_749_, v_mask_750_, v_i_751_, v_type_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
stack->m_obj
 = v_res_861_;
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object* v_body_862_, lean_object* v_eqs_863_, lean_object* v_args_864_, lean_object* v_arg_865_, lean_object* v_mask_866_, lean_object* v_i_867_, lean_object* v_altType_868_, lean_object* v_numDiscrEqs_869_, lean_object* v_k_870_, lean_object* v_ys_871_, lean_object* v_eq_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_878_ = lean_expr_instantiate1(v_body_862_, v_eq_872_);
v___x_879_ = lean_array_push(v_eqs_863_, v_eq_872_);
v___x_880_ = lean_array_push(v_args_864_, v_arg_865_);
v___x_881_ = 0;
v___x_882_ = lean_box(v___x_881_);
v___x_883_ = lean_array_push(v_mask_866_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_i_867_, v___x_884_);
v___x_886_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_868_, v_numDiscrEqs_869_, v_k_870_, v_ys_871_, v___x_879_, v___x_880_, v___x_883_, v___x_885_, v___x_878_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
return v___x_886_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_862_ = stack[0].m_obj;
lean_object* v_eqs_863_ = stack[1].m_obj;
lean_object* v_args_864_ = stack[2].m_obj;
lean_object* v_arg_865_ = stack[3].m_obj;
lean_object* v_mask_866_ = stack[4].m_obj;
lean_object* v_i_867_ = stack[5].m_obj;
lean_object* v_altType_868_ = stack[6].m_obj;
lean_object* v_numDiscrEqs_869_ = stack[7].m_obj;
lean_object* v_k_870_ = stack[8].m_obj;
lean_object* v_ys_871_ = stack[9].m_obj;
lean_object* v_eq_872_ = stack[10].m_obj;
lean_object* v___y_873_ = stack[11].m_obj;
lean_object* v___y_874_ = stack[12].m_obj;
lean_object* v___y_875_ = stack[13].m_obj;
lean_object* v___y_876_ = stack[14].m_obj;
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_862_, v_eqs_863_, v_args_864_, v_arg_865_, v_mask_866_, v_i_867_, v_altType_868_, v_numDiscrEqs_869_, v_k_870_, v_ys_871_, v_eq_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object* v_altType_888_, lean_object* v_numDiscrEqs_889_, lean_object* v_k_890_, lean_object* v_ys_891_, lean_object* v_eqs_892_, lean_object* v_args_893_, lean_object* v_mask_894_, lean_object* v_i_895_, lean_object* v_type_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_888_, v_numDiscrEqs_889_, v_k_890_, v_ys_891_, v_eqs_892_, v_args_893_, v_mask_894_, v_i_895_, v_type_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
return v_res_902_;
}
}
lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object* v_00_u03b1_903_, lean_object* v_altType_904_, lean_object* v_numDiscrEqs_905_, lean_object* v_k_906_, lean_object* v_ys_907_, lean_object* v_eqs_908_, lean_object* v_args_909_, lean_object* v_mask_910_, lean_object* v_i_911_, lean_object* v_type_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_904_, v_numDiscrEqs_905_, v_k_906_, v_ys_907_, v_eqs_908_, v_args_909_, v_mask_910_, v_i_911_, v_type_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_918_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_904_ = stack[1].m_obj;
lean_object* v_numDiscrEqs_905_ = stack[2].m_obj;
lean_object* v_k_906_ = stack[3].m_obj;
lean_object* v_ys_907_ = stack[4].m_obj;
lean_object* v_eqs_908_ = stack[5].m_obj;
lean_object* v_args_909_ = stack[6].m_obj;
lean_object* v_mask_910_ = stack[7].m_obj;
lean_object* v_i_911_ = stack[8].m_obj;
lean_object* v_type_912_ = stack[9].m_obj;
lean_object* v_a_913_ = stack[10].m_obj;
lean_object* v_a_914_ = stack[11].m_obj;
lean_object* v_a_915_ = stack[12].m_obj;
lean_object* v_a_916_ = stack[13].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_box(0), v_altType_904_, v_numDiscrEqs_905_, v_k_906_, v_ys_907_, v_eqs_908_, v_args_909_, v_mask_910_, v_i_911_, v_type_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object* v_00_u03b1_920_, lean_object* v_altType_921_, lean_object* v_numDiscrEqs_922_, lean_object* v_k_923_, lean_object* v_ys_924_, lean_object* v_eqs_925_, lean_object* v_args_926_, lean_object* v_mask_927_, lean_object* v_i_928_, lean_object* v_type_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(v_00_u03b1_920_, v_altType_921_, v_numDiscrEqs_922_, v_k_923_, v_ys_924_, v_eqs_925_, v_args_926_, v_mask_927_, v_i_928_, v_type_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_935_;
}
}
lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object* v_altType_936_, lean_object* v_numDiscrEqs_937_, lean_object* v_k_938_, lean_object* v_ys_939_, lean_object* v_args_940_, lean_object* v_mask_941_, lean_object* v_altType_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_950_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_936_, v_numDiscrEqs_937_, v_k_938_, v_ys_939_, v___x_949_, v_args_940_, v_mask_941_, v___x_948_, v_altType_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_936_ = stack[0].m_obj;
lean_object* v_numDiscrEqs_937_ = stack[1].m_obj;
lean_object* v_k_938_ = stack[2].m_obj;
lean_object* v_ys_939_ = stack[3].m_obj;
lean_object* v_args_940_ = stack[4].m_obj;
lean_object* v_mask_941_ = stack[5].m_obj;
lean_object* v_altType_942_ = stack[6].m_obj;
lean_object* v___y_943_ = stack[7].m_obj;
lean_object* v___y_944_ = stack[8].m_obj;
lean_object* v___y_945_ = stack[9].m_obj;
lean_object* v___y_946_ = stack[10].m_obj;
lean_object* v_res_951_;
v_res_951_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_936_, v_numDiscrEqs_937_, v_k_938_, v_ys_939_, v_args_940_, v_mask_941_, v_altType_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object* v_altType_952_, lean_object* v_numDiscrEqs_953_, lean_object* v_k_954_, lean_object* v_ys_955_, lean_object* v_args_956_, lean_object* v_mask_957_, lean_object* v_altType_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_952_, v_numDiscrEqs_953_, v_k_954_, v_ys_955_, v_args_956_, v_mask_957_, v_altType_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object* v_altType_965_, lean_object* v_altInfo_966_, lean_object* v_numDiscrEqs_967_, lean_object* v_k_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___f_974_; lean_object* v___x_975_; 
lean_inc_ref(v_altType_965_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_974_, 0, v_altType_965_);
lean_closure_set(v___f_974_, 1, v_numDiscrEqs_967_);
lean_closure_set(v___f_974_, 2, v_k_968_);
v___x_975_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_965_, v_altInfo_966_, v___f_974_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_975_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_forallAltTelescope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_965_ = stack[0].m_obj;
lean_object* v_altInfo_966_ = stack[1].m_obj;
lean_object* v_numDiscrEqs_967_ = stack[2].m_obj;
lean_object* v_k_968_ = stack[3].m_obj;
lean_object* v_a_969_ = stack[4].m_obj;
lean_object* v_a_970_ = stack[5].m_obj;
lean_object* v_a_971_ = stack[6].m_obj;
lean_object* v_a_972_ = stack[7].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_965_, v_altInfo_966_, v_numDiscrEqs_967_, v_k_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object* v_altType_977_, lean_object* v_altInfo_978_, lean_object* v_numDiscrEqs_979_, lean_object* v_k_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_977_, v_altInfo_978_, v_numDiscrEqs_979_, v_k_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_986_;
}
}
lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object* v_00_u03b1_987_, lean_object* v_altType_988_, lean_object* v_altInfo_989_, lean_object* v_numDiscrEqs_990_, lean_object* v_k_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_988_, v_altInfo_989_, v_numDiscrEqs_990_, v_k_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_997_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_forallAltTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_altType_988_ = stack[1].m_obj;
lean_object* v_altInfo_989_ = stack[2].m_obj;
lean_object* v_numDiscrEqs_990_ = stack[3].m_obj;
lean_object* v_k_991_ = stack[4].m_obj;
lean_object* v_a_992_ = stack[5].m_obj;
lean_object* v_a_993_ = stack[6].m_obj;
lean_object* v_a_994_ = stack[7].m_obj;
lean_object* v_a_995_ = stack[8].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_Meta_Match_forallAltTelescope(lean_box(0), v_altType_988_, v_altInfo_989_, v_numDiscrEqs_990_, v_k_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object* v_00_u03b1_999_, lean_object* v_altType_1000_, lean_object* v_altInfo_1001_, lean_object* v_numDiscrEqs_1002_, lean_object* v_k_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_Match_forallAltTelescope(v_00_u03b1_999_, v_altType_1000_, v_altInfo_1001_, v_numDiscrEqs_1002_, v_k_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1009_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_AltTelescopes(builtin);
}
#ifdef __cplusplus
}
#endif
