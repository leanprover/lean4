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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(lean_object* v_h_1_, lean_object* v_e_2_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed(lean_object* v_h_8_, lean_object* v_e_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(v_h_8_, v_e_9_);
lean_dec_ref(v_e_9_);
lean_dec_ref(v_h_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(lean_object* v_type_12_, lean_object* v_h_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; 
v___f_14_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed), 2, 1);
lean_closure_set(v___f_14_, 0, v_h_13_);
v___x_15_ = lean_find_expr(v___f_14_, v_type_12_);
lean_dec_ref(v___f_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = 1;
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___boxed(lean_object* v_type_18_, lean_object* v_h_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v_type_18_, v_h_19_);
lean_dec_ref(v_type_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_2005__overap_30_; lean_object* v___x_31_; 
v___f_29_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_2005__overap_30_ = lean_panic_fn_borrowed(v___f_29_, v_msg_23_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
lean_inc(v___y_25_);
lean_inc_ref(v___y_24_);
v___x_31_ = lean_apply_5(v___x_2005__overap_30_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, lean_box(0));
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___boxed(lean_object* v_msg_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v_msg_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(lean_object* v_xs_39_, lean_object* v_v_40_, lean_object* v_i_41_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_array_get_size(v_xs_39_);
v___x_43_ = lean_nat_dec_lt(v_i_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
lean_dec(v_i_41_);
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_array_fget_borrowed(v_xs_39_, v_i_41_);
v___x_46_ = lean_expr_eqv(v___x_45_, v_v_40_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_i_41_, v___x_47_);
lean_dec(v_i_41_);
v_i_41_ = v___x_48_;
goto _start;
}
else
{
lean_object* v___x_50_; 
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v_i_41_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2___boxed(lean_object* v_xs_51_, lean_object* v_v_52_, lean_object* v_i_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_51_, v_v_52_, v_i_53_);
lean_dec_ref(v_v_52_);
lean_dec_ref(v_xs_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(lean_object* v_xs_55_, lean_object* v_v_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_55_, v_v_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1___boxed(lean_object* v_xs_59_, lean_object* v_v_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_59_, v_v_60_);
lean_dec_ref(v_v_60_);
lean_dec_ref(v_xs_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(lean_object* v_xs_62_, lean_object* v_v_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_62_, v_v_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_val_66_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_64_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_dec(v___x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_val_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2___boxed(lean_object* v_xs_74_, lean_object* v_v_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_xs_74_, v_v_75_);
lean_dec_ref(v_v_75_);
lean_dec_ref(v_xs_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(lean_object* v_msgData_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v_toCold_86_; lean_object* v_mctx_87_; lean_object* v_lctx_88_; lean_object* v_options_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_env_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_83_);
v___x_85_ = lean_st_ref_get(v___y_79_);
v_toCold_86_ = lean_ctor_get(v___y_80_, 0);
v_mctx_87_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_mctx_87_);
lean_dec(v___x_85_);
v_lctx_88_ = lean_ctor_get(v___y_78_, 2);
v_options_89_ = lean_ctor_get(v_toCold_86_, 2);
lean_inc_ref(v_options_89_);
lean_inc_ref(v_lctx_88_);
v___x_90_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_90_, 0, v_env_84_);
lean_ctor_set(v___x_90_, 1, v_mctx_87_);
lean_ctor_set(v___x_90_, 2, v_lctx_88_);
lean_ctor_set(v___x_90_, 3, v_options_89_);
v___x_91_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_msgData_77_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(lean_object* v_msgData_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_ref_106_; lean_object* v___x_107_; lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
v_ref_106_ = lean_ctor_get(v___y_103_, 2);
v___x_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_116_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
lean_inc(v_ref_106_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v_ref_106_);
lean_ctor_set(v___x_112_, 1, v_a_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 1);
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(lean_object* v_k_124_, lean_object* v_b_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
v___x_131_ = lean_apply_6(v_k_124_, v_b_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, lean_box(0));
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_132_, lean_object* v_b_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_132_, v_b_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(lean_object* v_name_140_, uint8_t v_bi_141_, lean_object* v_type_142_, lean_object* v_k_143_, uint8_t v_kind_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___f_150_; lean_object* v___x_151_; 
v___f_150_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_150_, 0, v_k_143_);
v___x_151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_140_, v_bi_141_, v_type_142_, v___f_150_, v_kind_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_151_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_151_);
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
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(lean_object* v_name_168_, lean_object* v_bi_169_, lean_object* v_type_170_, lean_object* v_k_171_, lean_object* v_kind_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
uint8_t v_bi_boxed_178_; uint8_t v_kind_boxed_179_; lean_object* v_res_180_; 
v_bi_boxed_178_ = lean_unbox(v_bi_169_);
v_kind_boxed_179_ = lean_unbox(v_kind_172_);
v_res_180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_168_, v_bi_boxed_178_, v_type_170_, v_k_171_, v_kind_boxed_179_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(lean_object* v_name_181_, lean_object* v_type_182_, lean_object* v_k_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; 
v___x_189_ = 0;
v___x_190_ = 0;
v___x_191_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_181_, v___x_189_, v_type_182_, v_k_183_, v___x_190_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(lean_object* v_name_192_, lean_object* v_type_193_, lean_object* v_k_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_192_, v_type_193_, v_k_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(lean_object* v_fst_201_, lean_object* v_snd_202_, size_t v_sz_203_, size_t v_i_204_, lean_object* v_bs_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_206_ == 0)
{
lean_dec_ref(v_snd_202_);
return v_bs_205_;
}
else
{
lean_object* v_v_207_; lean_object* v___x_208_; lean_object* v_bs_x27_209_; lean_object* v___y_211_; uint8_t v___x_216_; 
v_v_207_ = lean_array_uget(v_bs_205_, v_i_204_);
v___x_208_ = lean_unsigned_to_nat(0u);
v_bs_x27_209_ = lean_array_uset(v_bs_205_, v_i_204_, v___x_208_);
v___x_216_ = lean_expr_eqv(v_v_207_, v_fst_201_);
if (v___x_216_ == 0)
{
v___y_211_ = v_v_207_;
goto v___jp_210_;
}
else
{
lean_dec(v_v_207_);
lean_inc_ref(v_snd_202_);
v___y_211_ = v_snd_202_;
goto v___jp_210_;
}
v___jp_210_:
{
size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_204_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_209_, v_i_204_, v___y_211_);
v_i_204_ = v___x_213_;
v_bs_205_ = v___x_214_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(lean_object* v_fst_217_, lean_object* v_snd_218_, lean_object* v_sz_219_, lean_object* v_i_220_, lean_object* v_bs_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_219_);
lean_dec(v_sz_219_);
v_i_boxed_223_ = lean_unbox_usize(v_i_220_);
lean_dec(v_i_220_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_217_, v_snd_218_, v_sz_boxed_222_, v_i_boxed_223_, v_bs_221_);
lean_dec_ref(v_fst_217_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(lean_object* v_a_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_eq(v_i_227_, v_stop_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_uget_borrowed(v_as_226_, v_i_227_);
v___x_231_ = lean_expr_eqv(v_a_225_, v___x_230_);
if (v___x_231_ == 0)
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_227_, v___x_232_);
v_i_227_ = v___x_233_;
goto _start;
}
else
{
return v___x_231_;
}
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(lean_object* v_a_236_, lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_stop_239_){
_start:
{
size_t v_i_boxed_240_; size_t v_stop_boxed_241_; uint8_t v_res_242_; lean_object* v_r_243_; 
v_i_boxed_240_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_stop_boxed_241_ = lean_unbox_usize(v_stop_239_);
lean_dec(v_stop_239_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_236_, v_as_237_, v_i_boxed_240_, v_stop_boxed_241_);
lean_dec_ref(v_as_237_);
lean_dec_ref(v_a_236_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(lean_object* v_as_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_array_get_size(v_as_244_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
return v___x_248_;
}
else
{
if (v___x_248_ == 0)
{
return v___x_248_;
}
else
{
size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; 
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_247_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_245_, v_as_244_, v___x_249_, v___x_250_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(lean_object* v_as_252_, lean_object* v_a_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_252_, v_a_253_);
lean_dec_ref(v_a_253_);
lean_dec_ref(v_as_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(lean_object* v_altType_262_, lean_object* v_altInfo_263_, lean_object* v_k_264_, lean_object* v_ys_265_, lean_object* v_args_266_, lean_object* v_mask_267_, lean_object* v_i_268_, lean_object* v_type_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_262_, v_altInfo_263_, v_k_264_, v_ys_265_, v_args_266_, v_mask_267_, v_i_268_, v_type_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_280_ = lean_unsigned_to_nat(47u);
v___x_281_ = lean_unsigned_to_nat(68u);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_284_ = l_mkPanicMessageWithDecl(v___x_283_, v___x_282_, v___x_281_, v___x_280_, v___x_279_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_286_ = lean_unsigned_to_nat(48u);
v___x_287_ = lean_unsigned_to_nat(66u);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_290_ = l_mkPanicMessageWithDecl(v___x_289_, v___x_288_, v___x_287_, v___x_286_, v___x_285_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object* v_body_291_, lean_object* v_ys_292_, lean_object* v_args_293_, lean_object* v_mask_294_, uint8_t v___x_295_, lean_object* v_i_296_, lean_object* v_altType_297_, lean_object* v_altInfo_298_, lean_object* v_k_299_, lean_object* v_a_300_, lean_object* v_y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_316_; 
v___x_307_ = lean_expr_instantiate1(v_body_291_, v_y_301_);
v___x_316_ = l_Lean_Meta_matchEq_x3f(v_a_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
if (lean_obj_tag(v_a_317_) == 1)
{
lean_object* v_val_318_; lean_object* v_snd_319_; lean_object* v_fst_320_; lean_object* v_snd_321_; uint8_t v___y_323_; uint8_t v___x_378_; 
v_val_318_ = lean_ctor_get(v_a_317_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_a_317_, 1);
v_snd_319_ = lean_ctor_get(v_val_318_, 1);
lean_inc(v_snd_319_);
lean_dec(v_val_318_);
v_fst_320_ = lean_ctor_get(v_snd_319_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_snd_319_, 1);
lean_inc(v_snd_321_);
lean_dec(v_snd_319_);
v___x_378_ = l_Lean_Expr_isFVar(v_fst_320_);
if (v___x_378_ == 0)
{
v___y_323_ = v___x_378_;
goto v___jp_322_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_292_, v_fst_320_);
v___y_323_ = v___x_379_;
goto v___jp_322_;
}
v___jp_322_:
{
if (v___y_323_ == 0)
{
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
goto v___jp_308_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_293_, v_fst_320_);
if (v___x_324_ == 0)
{
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
goto v___jp_308_;
}
else
{
uint8_t v___x_325_; 
lean_inc_ref(v_y_301_);
v___x_325_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_307_, v_y_301_);
if (v___x_325_ == 0)
{
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
goto v___jp_308_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_292_, v_fst_320_);
if (lean_obj_tag(v___x_326_) == 1)
{
lean_object* v_val_327_; lean_object* v___x_328_; 
v_val_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_293_, v_fst_320_);
if (lean_obj_tag(v___x_328_) == 1)
{
lean_object* v_val_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; size_t v_sz_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = l_Array_eraseIdx___redArg(v_ys_292_, v_val_327_);
v___x_331_ = 0;
v___x_332_ = lean_box(v___x_331_);
v___x_333_ = lean_array_set(v_mask_294_, v_val_329_, v___x_332_);
lean_dec(v_val_329_);
v_sz_334_ = lean_array_size(v_args_293_);
v___x_335_ = ((size_t)0ULL);
lean_inc_n(v_snd_321_, 2);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_320_, v_snd_321_, v_sz_334_, v___x_335_, v_args_293_);
v___x_337_ = l_Lean_Meta_mkEqRefl(v_snd_321_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_n(v_a_338_, 2);
lean_dec_ref_known(v___x_337_, 1);
lean_inc(v_fst_320_);
v___x_339_ = l_Lean_Expr_replaceFVar(v___x_307_, v_fst_320_, v_snd_321_);
lean_dec_ref(v___x_307_);
v___x_340_ = l_Lean_Expr_fvarId_x21(v_fst_320_);
lean_dec(v_fst_320_);
v___x_341_ = l_Lean_Expr_fvarId_x21(v_y_301_);
lean_dec_ref(v_y_301_);
v___x_342_ = lean_array_push(v___x_336_, v_a_338_);
v___x_343_ = lean_box(v___x_331_);
v___x_344_ = lean_array_push(v___x_333_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_i_296_, v___x_345_);
v___x_347_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed), 13, 8);
lean_closure_set(v___x_347_, 0, v_altType_297_);
lean_closure_set(v___x_347_, 1, v_altInfo_298_);
lean_closure_set(v___x_347_, 2, v_k_299_);
lean_closure_set(v___x_347_, 3, v___x_330_);
lean_closure_set(v___x_347_, 4, v___x_342_);
lean_closure_set(v___x_347_, 5, v___x_344_);
lean_closure_set(v___x_347_, 6, v___x_346_);
lean_closure_set(v___x_347_, 7, v___x_339_);
v___x_348_ = lean_alloc_closure((void*)(l_Lean_Meta_withReplaceFVarId___boxed), 9, 4);
lean_closure_set(v___x_348_, 0, lean_box(0));
lean_closure_set(v___x_348_, 1, v___x_341_);
lean_closure_set(v___x_348_, 2, v_a_338_);
lean_closure_set(v___x_348_, 3, v___x_347_);
v___x_349_ = l_Lean_Meta_withReplaceFVarId___redArg(v___x_340_, v_snd_321_, v___x_348_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v___x_336_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_330_);
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
lean_dec_ref(v___x_307_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
v_a_350_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v___x_328_);
lean_dec(v_val_327_);
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
v___x_358_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
v___x_359_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_358_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_dec_ref_known(v___x_359_, 1);
goto v___jp_308_;
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
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
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v___x_326_);
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
v___x_368_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
v___x_369_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_368_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_dec_ref_known(v___x_369_, 1);
goto v___jp_308_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
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
}
}
}
}
}
else
{
lean_dec(v_a_317_);
goto v___jp_308_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_380_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_316_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_316_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
v___jp_308_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc_ref(v_y_301_);
v___x_309_ = lean_array_push(v_ys_292_, v_y_301_);
v___x_310_ = lean_array_push(v_args_293_, v_y_301_);
v___x_311_ = lean_box(v___x_295_);
v___x_312_ = lean_array_push(v_mask_294_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_i_296_, v___x_313_);
v___x_315_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_297_, v_altInfo_298_, v_k_299_, v___x_309_, v___x_310_, v___x_312_, v___x_314_, v___x_307_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object* v_body_388_, lean_object* v_ys_389_, lean_object* v_args_390_, lean_object* v_mask_391_, lean_object* v___x_392_, lean_object* v_i_393_, lean_object* v_altType_394_, lean_object* v_altInfo_395_, lean_object* v_k_396_, lean_object* v_a_397_, lean_object* v_y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_4050__boxed_404_; lean_object* v_res_405_; 
v___x_4050__boxed_404_ = lean_unbox(v___x_392_);
v_res_405_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_body_388_, v_ys_389_, v_args_390_, v_mask_391_, v___x_4050__boxed_404_, v_i_393_, v_altType_394_, v_altInfo_395_, v_k_396_, v_a_397_, v_y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v_i_393_);
lean_dec_ref(v_body_388_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(lean_object* v_altType_406_, lean_object* v_altInfo_407_, lean_object* v_k_408_, lean_object* v_ys_409_, lean_object* v_args_410_, lean_object* v_mask_411_, lean_object* v_i_412_, lean_object* v_type_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_whnfForall(v_type_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_numFields_421_; uint8_t v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v_numFields_421_ = lean_ctor_get(v_altInfo_407_, 0);
v___x_422_ = lean_nat_dec_lt(v_i_412_, v_numFields_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v_i_412_);
lean_dec_ref(v_altInfo_407_);
lean_dec_ref(v_altType_406_);
v___x_423_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_420_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
lean_inc(v_a_417_);
lean_inc_ref(v_a_416_);
lean_inc(v_a_415_);
lean_inc_ref(v_a_414_);
v___x_425_ = lean_apply_9(v_k_408_, v_ys_409_, v_args_410_, v_mask_411_, v_a_424_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, lean_box(0));
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_mask_411_);
lean_dec_ref(v_args_410_);
lean_dec_ref(v_ys_409_);
lean_dec_ref(v_k_408_);
v_a_426_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_423_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_420_) == 7)
{
lean_object* v_binderName_434_; lean_object* v_binderType_435_; lean_object* v_body_436_; lean_object* v___x_437_; 
v_binderName_434_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_binderName_434_);
v_binderType_435_ = lean_ctor_get(v_a_420_, 1);
lean_inc_ref(v_binderType_435_);
v_body_436_ = lean_ctor_get(v_a_420_, 2);
lean_inc_ref(v_body_436_);
lean_dec_ref_known(v_a_420_, 3);
v___x_437_ = l_Lean_Meta_Match_unfoldNamedPattern(v_binderType_435_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___f_440_; lean_object* v___x_441_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_n(v_a_438_, 2);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_box(v___x_422_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_440_, 0, v_body_436_);
lean_closure_set(v___f_440_, 1, v_ys_409_);
lean_closure_set(v___f_440_, 2, v_args_410_);
lean_closure_set(v___f_440_, 3, v_mask_411_);
lean_closure_set(v___f_440_, 4, v___x_439_);
lean_closure_set(v___f_440_, 5, v_i_412_);
lean_closure_set(v___f_440_, 6, v_altType_406_);
lean_closure_set(v___f_440_, 7, v_altInfo_407_);
lean_closure_set(v___f_440_, 8, v_k_408_);
lean_closure_set(v___f_440_, 9, v_a_438_);
v___x_441_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_434_, v_a_438_, v___f_440_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_body_436_);
lean_dec(v_binderName_434_);
lean_dec(v_i_412_);
lean_dec_ref(v_mask_411_);
lean_dec_ref(v_args_410_);
lean_dec_ref(v_ys_409_);
lean_dec_ref(v_k_408_);
lean_dec_ref(v_altInfo_407_);
lean_dec_ref(v_altType_406_);
v_a_442_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_437_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
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
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_inc(v_numFields_421_);
lean_dec(v_a_420_);
lean_dec(v_i_412_);
lean_dec_ref(v_mask_411_);
lean_dec_ref(v_args_410_);
lean_dec_ref(v_ys_409_);
lean_dec_ref(v_k_408_);
lean_dec_ref(v_altInfo_407_);
v___x_450_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_451_ = l_Nat_reprFast(v_numFields_421_);
v___x_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = l_Lean_MessageData_ofFormat(v___x_452_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_450_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_indentExpr(v_altType_406_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_458_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_459_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_i_412_);
lean_dec_ref(v_mask_411_);
lean_dec_ref(v_args_410_);
lean_dec_ref(v_ys_409_);
lean_dec_ref(v_k_408_);
lean_dec_ref(v_altInfo_407_);
lean_dec_ref(v_altType_406_);
v_a_460_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_419_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_419_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_object* v_00_u03b1_468_, lean_object* v_altType_469_, lean_object* v_altInfo_470_, lean_object* v_k_471_, lean_object* v_ys_472_, lean_object* v_args_473_, lean_object* v_mask_474_, lean_object* v_i_475_, lean_object* v_type_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_469_, v_altInfo_470_, v_k_471_, v_ys_472_, v_args_473_, v_mask_474_, v_i_475_, v_type_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(lean_object* v_00_u03b1_483_, lean_object* v_altType_484_, lean_object* v_altInfo_485_, lean_object* v_k_486_, lean_object* v_ys_487_, lean_object* v_args_488_, lean_object* v_mask_489_, lean_object* v_i_490_, lean_object* v_type_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(v_00_u03b1_483_, v_altType_484_, v_altInfo_485_, v_k_486_, v_ys_487_, v_args_488_, v_mask_489_, v_i_490_, v_type_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_object* v_00_u03b1_498_, lean_object* v_name_499_, uint8_t v_bi_500_, lean_object* v_type_501_, lean_object* v_k_502_, uint8_t v_kind_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_499_, v_bi_500_, v_type_501_, v_k_502_, v_kind_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_510_, lean_object* v_name_511_, lean_object* v_bi_512_, lean_object* v_type_513_, lean_object* v_k_514_, lean_object* v_kind_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v_bi_boxed_521_; uint8_t v_kind_boxed_522_; lean_object* v_res_523_; 
v_bi_boxed_521_ = lean_unbox(v_bi_512_);
v_kind_boxed_522_ = lean_unbox(v_kind_515_);
v_res_523_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(v_00_u03b1_510_, v_name_511_, v_bi_boxed_521_, v_type_513_, v_k_514_, v_kind_boxed_522_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_object* v_00_u03b1_524_, lean_object* v_name_525_, lean_object* v_type_526_, lean_object* v_k_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_525_, v_type_526_, v_k_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(lean_object* v_00_u03b1_534_, lean_object* v_name_535_, lean_object* v_type_536_, lean_object* v_k_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(v_00_u03b1_534_, v_name_535_, v_type_536_, v_k_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_object* v_00_u03b1_544_, lean_object* v_msg_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(lean_object* v_00_u03b1_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(v_00_u03b1_552_, v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___f_566_; lean_object* v___x_403__overap_567_; lean_object* v___x_568_; 
v___f_566_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_403__overap_567_ = lean_panic_fn_borrowed(v___f_566_, v_msg_560_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
v___x_568_ = lean_apply_5(v___x_403__overap_567_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, lean_box(0));
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_object* v_00_u03b1_576_, lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(lean_object* v_00_u03b1_584_, lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(v_00_u03b1_584_, v_msg_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_591_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1));
v___x_595_ = lean_unsigned_to_nat(2u);
v___x_596_ = lean_unsigned_to_nat(45u);
v___x_597_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0));
v___x_598_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_599_ = l_mkPanicMessageWithDecl(v___x_598_, v___x_597_, v___x_596_, v___x_595_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
v___x_608_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6));
v___x_609_ = l_Lean_mkConst(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_mk_empty_array_with_capacity(v___x_611_);
v___x_613_ = lean_array_push(v___x_612_, v___x_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object* v_altType_619_, lean_object* v_altInfo_620_, lean_object* v_k_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_numOverlaps_627_; uint8_t v_hasUnitThunk_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_numOverlaps_627_ = lean_ctor_get(v_altInfo_620_, 1);
v_hasUnitThunk_628_ = lean_ctor_get_uint8(v_altInfo_620_, sizeof(void*)*2);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_eq(v_numOverlaps_627_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v_k_621_);
lean_dec_ref(v_altInfo_620_);
lean_dec_ref(v_altType_619_);
v___x_631_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2);
v___x_632_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v___x_631_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
return v___x_632_;
}
else
{
if (v_hasUnitThunk_628_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
lean_inc_ref(v_altType_619_);
v___x_634_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_619_, v_altInfo_620_, v_k_621_, v___x_633_, v___x_633_, v___x_633_, v___x_629_, v_altType_619_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_altInfo_620_);
v___x_635_ = l_Lean_Meta_whnfForall(v_altType_619_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_636_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8);
v___x_640_ = l_Lean_Meta_instantiateForall(v_a_638_, v___x_639_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_643_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9));
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
v___x_644_ = lean_apply_9(v_k_621_, v___x_642_, v___x_639_, v___x_643_, v_a_641_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_k_621_);
v_a_645_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_640_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_640_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_k_621_);
v_a_653_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_637_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_637_);
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
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_k_621_);
v_a_661_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_635_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_635_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(lean_object* v_altType_669_, lean_object* v_altInfo_670_, lean_object* v_k_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_669_, v_altInfo_670_, v_k_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope(lean_object* v_00_u03b1_678_, lean_object* v_altType_679_, lean_object* v_altInfo_680_, lean_object* v_k_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_679_, v_altInfo_680_, v_k_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___boxed(lean_object* v_00_u03b1_688_, lean_object* v_altType_689_, lean_object* v_altInfo_690_, lean_object* v_k_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_Match_forallAltVarsTelescope(v_00_u03b1_688_, v_altType_689_, v_altInfo_690_, v_k_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(lean_object* v_body_698_, lean_object* v_eqs_699_, lean_object* v_args_700_, lean_object* v_arg_701_, lean_object* v_mask_702_, lean_object* v_i_703_, lean_object* v_altType_704_, lean_object* v_numDiscrEqs_705_, lean_object* v_k_706_, lean_object* v_ys_707_, lean_object* v_eq_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_698_, v_eqs_699_, v_args_700_, v_arg_701_, v_mask_702_, v_i_703_, v_altType_704_, v_numDiscrEqs_705_, v_k_706_, v_ys_707_, v_eq_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_i_703_);
lean_dec_ref(v_body_698_);
return v_res_714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2));
v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(lean_object* v_altType_721_, lean_object* v_numDiscrEqs_722_, lean_object* v_k_723_, lean_object* v_ys_724_, lean_object* v_eqs_725_, lean_object* v_args_726_, lean_object* v_mask_727_, lean_object* v_i_728_, lean_object* v_type_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
uint8_t v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_nat_dec_lt(v_i_728_, v_numDiscrEqs_722_);
v___x_736_ = l_Lean_Meta_whnfForall(v_type_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
if (v___x_735_ == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
lean_dec(v_i_728_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_737_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
v___x_740_ = lean_apply_10(v_k_723_, v_ys_724_, v_eqs_725_, v_args_726_, v_mask_727_, v_a_739_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, lean_box(0));
return v___x_740_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
v_a_741_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_738_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_738_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_736_, 1);
if (lean_obj_tag(v_a_749_) == 7)
{
lean_object* v_binderName_750_; lean_object* v_binderType_751_; lean_object* v_body_752_; lean_object* v_arg_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___x_761_; 
v_binderName_750_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_binderName_750_);
v_binderType_751_ = lean_ctor_get(v_a_749_, 1);
lean_inc_ref_n(v_binderType_751_, 2);
v_body_752_ = lean_ctor_get(v_a_749_, 2);
lean_inc_ref(v_body_752_);
lean_dec_ref_known(v_a_749_, 3);
v___x_761_ = l_Lean_Meta_matchEq_x3f(v_binderType_751_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
if (lean_obj_tag(v_a_762_) == 1)
{
lean_object* v_val_763_; lean_object* v_snd_764_; lean_object* v_snd_765_; lean_object* v___x_766_; 
v_val_763_ = lean_ctor_get(v_a_762_, 0);
lean_inc(v_val_763_);
lean_dec_ref_known(v_a_762_, 1);
v_snd_764_ = lean_ctor_get(v_val_763_, 1);
lean_inc(v_snd_764_);
lean_dec(v_val_763_);
v_snd_765_ = lean_ctor_get(v_snd_764_, 1);
lean_inc(v_snd_765_);
lean_dec(v_snd_764_);
v___x_766_ = l_Lean_Meta_mkEqRefl(v_snd_765_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v_arg_754_ = v_a_767_;
v___y_755_ = v_a_730_;
v___y_756_ = v_a_731_;
v___y_757_ = v_a_732_;
v___y_758_ = v_a_733_;
goto v___jp_753_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_body_752_);
lean_dec_ref(v_binderType_751_);
lean_dec(v_binderName_750_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_768_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_766_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_a_762_);
lean_inc_ref(v_binderType_751_);
v___x_776_ = l_Lean_Meta_matchHEq_x3f(v_binderType_751_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
if (lean_obj_tag(v_a_777_) == 1)
{
lean_object* v_val_778_; lean_object* v_snd_779_; lean_object* v_snd_780_; lean_object* v_snd_781_; lean_object* v___x_782_; 
v_val_778_ = lean_ctor_get(v_a_777_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_a_777_, 1);
v_snd_779_ = lean_ctor_get(v_val_778_, 1);
lean_inc(v_snd_779_);
lean_dec(v_val_778_);
v_snd_780_ = lean_ctor_get(v_snd_779_, 1);
lean_inc(v_snd_780_);
lean_dec(v_snd_779_);
v_snd_781_ = lean_ctor_get(v_snd_780_, 1);
lean_inc(v_snd_781_);
lean_dec(v_snd_780_);
v___x_782_ = l_Lean_Meta_mkHEqRefl(v_snd_781_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v_arg_754_ = v_a_783_;
v___y_755_ = v_a_730_;
v___y_756_ = v_a_731_;
v___y_757_ = v_a_732_;
v___y_758_ = v_a_733_;
goto v___jp_753_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_body_752_);
lean_dec_ref(v_binderType_751_);
lean_dec(v_binderName_750_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_784_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_782_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_a_777_);
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
lean_inc_ref(v_altType_721_);
v___x_793_ = l_Lean_indentExpr(v_altType_721_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_794_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v_arg_754_ = v_a_796_;
v___y_755_ = v_a_730_;
v___y_756_ = v_a_731_;
v___y_757_ = v_a_732_;
v___y_758_ = v_a_733_;
goto v___jp_753_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_body_752_);
lean_dec_ref(v_binderType_751_);
lean_dec(v_binderName_750_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_body_752_);
lean_dec_ref(v_binderType_751_);
lean_dec(v_binderName_750_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_805_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_776_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_776_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_body_752_);
lean_dec_ref(v_binderType_751_);
lean_dec(v_binderName_750_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_813_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_761_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_761_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
v___jp_753_:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_759_, 0, v_body_752_);
lean_closure_set(v___f_759_, 1, v_eqs_725_);
lean_closure_set(v___f_759_, 2, v_args_726_);
lean_closure_set(v___f_759_, 3, v_arg_754_);
lean_closure_set(v___f_759_, 4, v_mask_727_);
lean_closure_set(v___f_759_, 5, v_i_728_);
lean_closure_set(v___f_759_, 6, v_altType_721_);
lean_closure_set(v___f_759_, 7, v_numDiscrEqs_722_);
lean_closure_set(v___f_759_, 8, v_k_723_);
lean_closure_set(v___f_759_, 9, v_ys_724_);
v___x_760_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_750_, v_binderType_751_, v___f_759_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_a_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
v___x_821_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_822_ = l_Nat_reprFast(v_numDiscrEqs_722_);
v___x_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = l_Lean_MessageData_ofFormat(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_821_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_indentExpr(v_altType_721_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_829_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_830_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_831_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_736_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_736_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object* v_body_839_, lean_object* v_eqs_840_, lean_object* v_args_841_, lean_object* v_arg_842_, lean_object* v_mask_843_, lean_object* v_i_844_, lean_object* v_altType_845_, lean_object* v_numDiscrEqs_846_, lean_object* v_k_847_, lean_object* v_ys_848_, lean_object* v_eq_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_855_ = lean_expr_instantiate1(v_body_839_, v_eq_849_);
v___x_856_ = lean_array_push(v_eqs_840_, v_eq_849_);
v___x_857_ = lean_array_push(v_args_841_, v_arg_842_);
v___x_858_ = 0;
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_array_push(v_mask_843_, v___x_859_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_i_844_, v___x_861_);
v___x_863_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_845_, v_numDiscrEqs_846_, v_k_847_, v_ys_848_, v___x_856_, v___x_857_, v___x_860_, v___x_862_, v___x_855_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object* v_altType_864_, lean_object* v_numDiscrEqs_865_, lean_object* v_k_866_, lean_object* v_ys_867_, lean_object* v_eqs_868_, lean_object* v_args_869_, lean_object* v_mask_870_, lean_object* v_i_871_, lean_object* v_type_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_864_, v_numDiscrEqs_865_, v_k_866_, v_ys_867_, v_eqs_868_, v_args_869_, v_mask_870_, v_i_871_, v_type_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object* v_00_u03b1_879_, lean_object* v_altType_880_, lean_object* v_numDiscrEqs_881_, lean_object* v_k_882_, lean_object* v_ys_883_, lean_object* v_eqs_884_, lean_object* v_args_885_, lean_object* v_mask_886_, lean_object* v_i_887_, lean_object* v_type_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_880_, v_numDiscrEqs_881_, v_k_882_, v_ys_883_, v_eqs_884_, v_args_885_, v_mask_886_, v_i_887_, v_type_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object* v_00_u03b1_895_, lean_object* v_altType_896_, lean_object* v_numDiscrEqs_897_, lean_object* v_k_898_, lean_object* v_ys_899_, lean_object* v_eqs_900_, lean_object* v_args_901_, lean_object* v_mask_902_, lean_object* v_i_903_, lean_object* v_type_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(v_00_u03b1_895_, v_altType_896_, v_numDiscrEqs_897_, v_k_898_, v_ys_899_, v_eqs_900_, v_args_901_, v_mask_902_, v_i_903_, v_type_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object* v_altType_911_, lean_object* v_numDiscrEqs_912_, lean_object* v_k_913_, lean_object* v_ys_914_, lean_object* v_args_915_, lean_object* v_mask_916_, lean_object* v_altType_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_925_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_911_, v_numDiscrEqs_912_, v_k_913_, v_ys_914_, v___x_924_, v_args_915_, v_mask_916_, v___x_923_, v_altType_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object* v_altType_926_, lean_object* v_numDiscrEqs_927_, lean_object* v_k_928_, lean_object* v_ys_929_, lean_object* v_args_930_, lean_object* v_mask_931_, lean_object* v_altType_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_926_, v_numDiscrEqs_927_, v_k_928_, v_ys_929_, v_args_930_, v_mask_931_, v_altType_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object* v_altType_939_, lean_object* v_altInfo_940_, lean_object* v_numDiscrEqs_941_, lean_object* v_k_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___f_948_; lean_object* v___x_949_; 
lean_inc_ref(v_altType_939_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_948_, 0, v_altType_939_);
lean_closure_set(v___f_948_, 1, v_numDiscrEqs_941_);
lean_closure_set(v___f_948_, 2, v_k_942_);
v___x_949_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_939_, v_altInfo_940_, v___f_948_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object* v_altType_950_, lean_object* v_altInfo_951_, lean_object* v_numDiscrEqs_952_, lean_object* v_k_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_950_, v_altInfo_951_, v_numDiscrEqs_952_, v_k_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object* v_00_u03b1_960_, lean_object* v_altType_961_, lean_object* v_altInfo_962_, lean_object* v_numDiscrEqs_963_, lean_object* v_k_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_961_, v_altInfo_962_, v_numDiscrEqs_963_, v_k_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object* v_00_u03b1_971_, lean_object* v_altType_972_, lean_object* v_altInfo_973_, lean_object* v_numDiscrEqs_974_, lean_object* v_k_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_Match_forallAltTelescope(v_00_u03b1_971_, v_altType_972_, v_altInfo_973_, v_numDiscrEqs_974_, v_k_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_981_;
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
