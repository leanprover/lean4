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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object* v_a_291_, lean_object* v_body_292_, lean_object* v_ys_293_, lean_object* v_args_294_, lean_object* v_mask_295_, uint8_t v___x_296_, lean_object* v_i_297_, lean_object* v_altType_298_, lean_object* v_altInfo_299_, lean_object* v_k_300_, lean_object* v_y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_matchEq_x3f(v_a_291_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = lean_expr_instantiate1(v_body_292_, v_y_301_);
if (lean_obj_tag(v_a_308_) == 1)
{
lean_object* v_val_322_; lean_object* v_snd_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; uint8_t v___y_327_; uint8_t v___x_382_; 
v_val_322_ = lean_ctor_get(v_a_308_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_a_308_, 1);
v_snd_323_ = lean_ctor_get(v_val_322_, 1);
lean_inc(v_snd_323_);
lean_dec(v_val_322_);
v_fst_324_ = lean_ctor_get(v_snd_323_, 0);
lean_inc(v_fst_324_);
v_snd_325_ = lean_ctor_get(v_snd_323_, 1);
lean_inc(v_snd_325_);
lean_dec(v_snd_323_);
v___x_382_ = l_Lean_Expr_isFVar(v_fst_324_);
if (v___x_382_ == 0)
{
v___y_327_ = v___x_382_;
goto v___jp_326_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_293_, v_fst_324_);
v___y_327_ = v___x_383_;
goto v___jp_326_;
}
v___jp_326_:
{
if (v___y_327_ == 0)
{
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_294_, v_fst_324_);
if (v___x_328_ == 0)
{
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
else
{
uint8_t v___x_329_; 
lean_inc_ref(v_y_301_);
v___x_329_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_309_, v_y_301_);
if (v___x_329_ == 0)
{
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_293_, v_fst_324_);
if (lean_obj_tag(v___x_330_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_332_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_294_, v_fst_324_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v___x_332_, 1);
lean_inc(v_snd_325_);
v___x_334_ = l_Lean_Meta_mkEqRefl(v_snd_325_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; size_t v_sz_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_n(v_a_335_, 2);
lean_dec_ref_known(v___x_334_, 1);
v_sz_336_ = lean_array_size(v_args_294_);
v___x_337_ = l_Array_eraseIdx___redArg(v_ys_293_, v_val_331_);
v___x_338_ = 0;
v___x_339_ = lean_box(v___x_338_);
v___x_340_ = lean_array_set(v_mask_295_, v_val_333_, v___x_339_);
lean_dec(v_val_333_);
v___x_341_ = ((size_t)0ULL);
lean_inc(v_snd_325_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_324_, v_snd_325_, v_sz_336_, v___x_341_, v_args_294_);
lean_inc(v_fst_324_);
v___x_343_ = l_Lean_Expr_replaceFVar(v___x_309_, v_fst_324_, v_snd_325_);
lean_dec_ref(v___x_309_);
v___x_344_ = l_Lean_Expr_fvarId_x21(v_fst_324_);
lean_dec(v_fst_324_);
v___x_345_ = l_Lean_Expr_fvarId_x21(v_y_301_);
lean_dec_ref(v_y_301_);
v___x_346_ = lean_array_push(v___x_342_, v_a_335_);
v___x_347_ = lean_box(v___x_338_);
v___x_348_ = lean_array_push(v___x_340_, v___x_347_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_i_297_, v___x_349_);
v___x_351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed), 13, 8);
lean_closure_set(v___x_351_, 0, v_altType_298_);
lean_closure_set(v___x_351_, 1, v_altInfo_299_);
lean_closure_set(v___x_351_, 2, v_k_300_);
lean_closure_set(v___x_351_, 3, v___x_337_);
lean_closure_set(v___x_351_, 4, v___x_346_);
lean_closure_set(v___x_351_, 5, v___x_348_);
lean_closure_set(v___x_351_, 6, v___x_350_);
lean_closure_set(v___x_351_, 7, v___x_343_);
v___x_352_ = lean_alloc_closure((void*)(l_Lean_Meta_withReplaceFVarId___boxed), 9, 4);
lean_closure_set(v___x_352_, 0, lean_box(0));
lean_closure_set(v___x_352_, 1, v___x_345_);
lean_closure_set(v___x_352_, 2, v_a_335_);
lean_closure_set(v___x_352_, 3, v___x_351_);
v___x_353_ = l_Lean_Meta_withReplaceFVarId___redArg(v___x_344_, v_snd_325_, v___x_352_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_353_;
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_val_333_);
lean_dec(v_val_331_);
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_300_);
lean_dec_ref(v_altInfo_299_);
lean_dec_ref(v_altType_298_);
lean_dec_ref(v_mask_295_);
lean_dec_ref(v_args_294_);
lean_dec_ref(v_ys_293_);
v_a_354_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_334_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_334_);
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
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v___x_332_);
lean_dec(v_val_331_);
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
v___x_363_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_362_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_dec_ref_known(v___x_363_, 1);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_300_);
lean_dec_ref(v_altInfo_299_);
lean_dec_ref(v_altType_298_);
lean_dec_ref(v_mask_295_);
lean_dec_ref(v_args_294_);
lean_dec_ref(v_ys_293_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v___x_330_);
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
v___x_373_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_372_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_dec_ref_known(v___x_373_, 1);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_300_);
lean_dec_ref(v_altInfo_299_);
lean_dec_ref(v_altType_298_);
lean_dec_ref(v_mask_295_);
lean_dec_ref(v_args_294_);
lean_dec_ref(v_ys_293_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
lean_dec(v_a_308_);
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
v___y_314_ = v___y_305_;
goto v___jp_310_;
}
v___jp_310_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_inc_ref(v_y_301_);
v___x_315_ = lean_array_push(v_ys_293_, v_y_301_);
v___x_316_ = lean_array_push(v_args_294_, v_y_301_);
v___x_317_ = lean_box(v___x_296_);
v___x_318_ = lean_array_push(v_mask_295_, v___x_317_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_i_297_, v___x_319_);
v___x_321_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_298_, v_altInfo_299_, v_k_300_, v___x_315_, v___x_316_, v___x_318_, v___x_320_, v___x_309_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_321_;
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v_y_301_);
lean_dec_ref(v_k_300_);
lean_dec_ref(v_altInfo_299_);
lean_dec_ref(v_altType_298_);
lean_dec_ref(v_mask_295_);
lean_dec_ref(v_args_294_);
lean_dec_ref(v_ys_293_);
v_a_384_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_307_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_307_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object* v_a_392_, lean_object* v_body_393_, lean_object* v_ys_394_, lean_object* v_args_395_, lean_object* v_mask_396_, lean_object* v___x_397_, lean_object* v_i_398_, lean_object* v_altType_399_, lean_object* v_altInfo_400_, lean_object* v_k_401_, lean_object* v_y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_4053__boxed_408_; lean_object* v_res_409_; 
v___x_4053__boxed_408_ = lean_unbox(v___x_397_);
v_res_409_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_a_392_, v_body_393_, v_ys_394_, v_args_395_, v_mask_396_, v___x_4053__boxed_408_, v_i_398_, v_altType_399_, v_altInfo_400_, v_k_401_, v_y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v_i_398_);
lean_dec_ref(v_body_393_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(lean_object* v_altType_410_, lean_object* v_altInfo_411_, lean_object* v_k_412_, lean_object* v_ys_413_, lean_object* v_args_414_, lean_object* v_mask_415_, lean_object* v_i_416_, lean_object* v_type_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_whnfForall(v_type_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_numFields_425_; uint8_t v___x_426_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v_numFields_425_ = lean_ctor_get(v_altInfo_411_, 0);
v___x_426_ = lean_nat_dec_lt(v_i_416_, v_numFields_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec(v_i_416_);
lean_dec_ref(v_altInfo_411_);
lean_dec_ref(v_altType_410_);
v___x_427_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_424_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
v___x_429_ = lean_apply_9(v_k_412_, v_ys_413_, v_args_414_, v_mask_415_, v_a_428_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, lean_box(0));
return v___x_429_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_mask_415_);
lean_dec_ref(v_args_414_);
lean_dec_ref(v_ys_413_);
lean_dec_ref(v_k_412_);
v_a_430_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_427_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_424_) == 7)
{
lean_object* v_binderName_438_; lean_object* v_binderType_439_; lean_object* v_body_440_; lean_object* v___x_441_; 
v_binderName_438_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_binderName_438_);
v_binderType_439_ = lean_ctor_get(v_a_424_, 1);
lean_inc_ref(v_binderType_439_);
v_body_440_ = lean_ctor_get(v_a_424_, 2);
lean_inc_ref(v_body_440_);
lean_dec_ref_known(v_a_424_, 3);
v___x_441_ = l_Lean_Meta_Match_unfoldNamedPattern(v_binderType_439_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_n(v_a_442_, 2);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_box(v___x_426_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_444_, 0, v_a_442_);
lean_closure_set(v___f_444_, 1, v_body_440_);
lean_closure_set(v___f_444_, 2, v_ys_413_);
lean_closure_set(v___f_444_, 3, v_args_414_);
lean_closure_set(v___f_444_, 4, v_mask_415_);
lean_closure_set(v___f_444_, 5, v___x_443_);
lean_closure_set(v___f_444_, 6, v_i_416_);
lean_closure_set(v___f_444_, 7, v_altType_410_);
lean_closure_set(v___f_444_, 8, v_altInfo_411_);
lean_closure_set(v___f_444_, 9, v_k_412_);
v___x_445_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_438_, v_a_442_, v___f_444_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_body_440_);
lean_dec(v_binderName_438_);
lean_dec(v_i_416_);
lean_dec_ref(v_mask_415_);
lean_dec_ref(v_args_414_);
lean_dec_ref(v_ys_413_);
lean_dec_ref(v_k_412_);
lean_dec_ref(v_altInfo_411_);
lean_dec_ref(v_altType_410_);
v_a_446_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_441_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_441_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_numFields_425_);
lean_dec(v_a_424_);
lean_dec(v_i_416_);
lean_dec_ref(v_mask_415_);
lean_dec_ref(v_args_414_);
lean_dec_ref(v_ys_413_);
lean_dec_ref(v_k_412_);
lean_dec_ref(v_altInfo_411_);
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_455_ = l_Nat_reprFast(v_numFields_425_);
v___x_456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = l_Lean_MessageData_ofFormat(v___x_456_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_454_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_indentExpr(v_altType_410_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_462_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
return v___x_463_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_i_416_);
lean_dec_ref(v_mask_415_);
lean_dec_ref(v_args_414_);
lean_dec_ref(v_ys_413_);
lean_dec_ref(v_k_412_);
lean_dec_ref(v_altInfo_411_);
lean_dec_ref(v_altType_410_);
v_a_464_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_423_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_423_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_object* v_00_u03b1_472_, lean_object* v_altType_473_, lean_object* v_altInfo_474_, lean_object* v_k_475_, lean_object* v_ys_476_, lean_object* v_args_477_, lean_object* v_mask_478_, lean_object* v_i_479_, lean_object* v_type_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_473_, v_altInfo_474_, v_k_475_, v_ys_476_, v_args_477_, v_mask_478_, v_i_479_, v_type_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(lean_object* v_00_u03b1_487_, lean_object* v_altType_488_, lean_object* v_altInfo_489_, lean_object* v_k_490_, lean_object* v_ys_491_, lean_object* v_args_492_, lean_object* v_mask_493_, lean_object* v_i_494_, lean_object* v_type_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(v_00_u03b1_487_, v_altType_488_, v_altInfo_489_, v_k_490_, v_ys_491_, v_args_492_, v_mask_493_, v_i_494_, v_type_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_object* v_00_u03b1_502_, lean_object* v_name_503_, uint8_t v_bi_504_, lean_object* v_type_505_, lean_object* v_k_506_, uint8_t v_kind_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_503_, v_bi_504_, v_type_505_, v_k_506_, v_kind_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_514_, lean_object* v_name_515_, lean_object* v_bi_516_, lean_object* v_type_517_, lean_object* v_k_518_, lean_object* v_kind_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_bi_boxed_525_; uint8_t v_kind_boxed_526_; lean_object* v_res_527_; 
v_bi_boxed_525_ = lean_unbox(v_bi_516_);
v_kind_boxed_526_ = lean_unbox(v_kind_519_);
v_res_527_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(v_00_u03b1_514_, v_name_515_, v_bi_boxed_525_, v_type_517_, v_k_518_, v_kind_boxed_526_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_object* v_00_u03b1_528_, lean_object* v_name_529_, lean_object* v_type_530_, lean_object* v_k_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_529_, v_type_530_, v_k_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(lean_object* v_00_u03b1_538_, lean_object* v_name_539_, lean_object* v_type_540_, lean_object* v_k_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(v_00_u03b1_538_, v_name_539_, v_type_540_, v_k_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_object* v_00_u03b1_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(lean_object* v_00_u03b1_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(v_00_u03b1_556_, v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_403__overap_571_; lean_object* v___x_572_; 
v___f_570_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_403__overap_571_ = lean_panic_fn_borrowed(v___f_570_, v_msg_564_);
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
v___x_572_ = lean_apply_5(v___x_403__overap_571_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, lean_box(0));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_object* v_00_u03b1_580_, lean_object* v_msg_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(lean_object* v_00_u03b1_588_, lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(v_00_u03b1_588_, v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1));
v___x_599_ = lean_unsigned_to_nat(2u);
v___x_600_ = lean_unsigned_to_nat(45u);
v___x_601_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0));
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_603_ = l_mkPanicMessageWithDecl(v___x_602_, v___x_601_, v___x_600_, v___x_599_, v___x_598_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
v___x_612_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6));
v___x_613_ = l_Lean_mkConst(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v___x_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object* v_altType_623_, lean_object* v_altInfo_624_, lean_object* v_k_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_numOverlaps_631_; uint8_t v_hasUnitThunk_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_numOverlaps_631_ = lean_ctor_get(v_altInfo_624_, 1);
v_hasUnitThunk_632_ = lean_ctor_get_uint8(v_altInfo_624_, sizeof(void*)*2);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_eq(v_numOverlaps_631_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v_k_625_);
lean_dec_ref(v_altInfo_624_);
lean_dec_ref(v_altType_623_);
v___x_635_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2);
v___x_636_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v___x_635_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_636_;
}
else
{
if (v_hasUnitThunk_632_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
lean_inc_ref(v_altType_623_);
v___x_638_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_623_, v_altInfo_624_, v_k_625_, v___x_637_, v___x_637_, v___x_637_, v___x_633_, v_altType_623_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec_ref(v_altInfo_624_);
v___x_639_ = l_Lean_Meta_whnfForall(v_altType_623_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_640_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8);
v___x_644_ = l_Lean_Meta_instantiateForall(v_a_642_, v___x_643_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_647_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9));
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
v___x_648_ = lean_apply_9(v_k_625_, v___x_646_, v___x_643_, v___x_647_, v_a_645_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, lean_box(0));
return v___x_648_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_k_625_);
v_a_649_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_644_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_k_625_);
v_a_657_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_641_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_641_);
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
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_k_625_);
v_a_665_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_639_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_639_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(lean_object* v_altType_673_, lean_object* v_altInfo_674_, lean_object* v_k_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_673_, v_altInfo_674_, v_k_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope(lean_object* v_00_u03b1_682_, lean_object* v_altType_683_, lean_object* v_altInfo_684_, lean_object* v_k_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_683_, v_altInfo_684_, v_k_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___boxed(lean_object* v_00_u03b1_692_, lean_object* v_altType_693_, lean_object* v_altInfo_694_, lean_object* v_k_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Match_forallAltVarsTelescope(v_00_u03b1_692_, v_altType_693_, v_altInfo_694_, v_k_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(lean_object* v_body_702_, lean_object* v_eqs_703_, lean_object* v_args_704_, lean_object* v_arg_705_, lean_object* v_mask_706_, lean_object* v_i_707_, lean_object* v_altType_708_, lean_object* v_numDiscrEqs_709_, lean_object* v_k_710_, lean_object* v_ys_711_, lean_object* v_eq_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_702_, v_eqs_703_, v_args_704_, v_arg_705_, v_mask_706_, v_i_707_, v_altType_708_, v_numDiscrEqs_709_, v_k_710_, v_ys_711_, v_eq_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v_i_707_);
lean_dec_ref(v_body_702_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(lean_object* v_altType_725_, lean_object* v_numDiscrEqs_726_, lean_object* v_k_727_, lean_object* v_ys_728_, lean_object* v_eqs_729_, lean_object* v_args_730_, lean_object* v_mask_731_, lean_object* v_i_732_, lean_object* v_type_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_whnfForall(v_type_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; uint8_t v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = lean_nat_dec_lt(v_i_732_, v_numDiscrEqs_726_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v_i_732_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v___x_742_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_740_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
v___x_744_ = lean_apply_10(v_k_727_, v_ys_728_, v_eqs_729_, v_args_730_, v_mask_731_, v_a_743_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_744_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
v_a_745_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_742_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_740_) == 7)
{
lean_object* v_binderName_753_; lean_object* v_binderType_754_; lean_object* v_body_755_; lean_object* v_arg_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_764_; 
v_binderName_753_ = lean_ctor_get(v_a_740_, 0);
lean_inc(v_binderName_753_);
v_binderType_754_ = lean_ctor_get(v_a_740_, 1);
lean_inc_ref_n(v_binderType_754_, 2);
v_body_755_ = lean_ctor_get(v_a_740_, 2);
lean_inc_ref(v_body_755_);
lean_dec_ref_known(v_a_740_, 3);
v___x_764_ = l_Lean_Meta_matchEq_x3f(v_binderType_754_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
if (lean_obj_tag(v_a_765_) == 1)
{
lean_object* v_val_766_; lean_object* v_snd_767_; lean_object* v_snd_768_; lean_object* v___x_769_; 
v_val_766_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_a_765_, 1);
v_snd_767_ = lean_ctor_get(v_val_766_, 1);
lean_inc(v_snd_767_);
lean_dec(v_val_766_);
v_snd_768_ = lean_ctor_get(v_snd_767_, 1);
lean_inc(v_snd_768_);
lean_dec(v_snd_767_);
v___x_769_ = l_Lean_Meta_mkEqRefl(v_snd_768_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v_arg_757_ = v_a_770_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
v___y_761_ = v_a_737_;
goto v___jp_756_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_754_);
lean_dec(v_binderName_753_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_771_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v___x_779_; 
lean_dec(v_a_765_);
lean_inc_ref(v_binderType_754_);
v___x_779_ = l_Lean_Meta_matchHEq_x3f(v_binderType_754_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
if (lean_obj_tag(v_a_780_) == 1)
{
lean_object* v_val_781_; lean_object* v_snd_782_; lean_object* v_snd_783_; lean_object* v_snd_784_; lean_object* v___x_785_; 
v_val_781_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_val_781_);
lean_dec_ref_known(v_a_780_, 1);
v_snd_782_ = lean_ctor_get(v_val_781_, 1);
lean_inc(v_snd_782_);
lean_dec(v_val_781_);
v_snd_783_ = lean_ctor_get(v_snd_782_, 1);
lean_inc(v_snd_783_);
lean_dec(v_snd_782_);
v_snd_784_ = lean_ctor_get(v_snd_783_, 1);
lean_inc(v_snd_784_);
lean_dec(v_snd_783_);
v___x_785_ = l_Lean_Meta_mkHEqRefl(v_snd_784_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v_arg_757_ = v_a_786_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
v___y_761_ = v_a_737_;
goto v___jp_756_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_754_);
lean_dec(v_binderName_753_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_787_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_785_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_a_780_);
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
lean_inc_ref(v_altType_725_);
v___x_796_ = l_Lean_indentExpr(v_altType_725_);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_797_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_arg_757_ = v_a_799_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
v___y_761_ = v_a_737_;
goto v___jp_756_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_754_);
lean_dec(v_binderName_753_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_800_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_798_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_754_);
lean_dec(v_binderName_753_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_808_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_779_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_779_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_754_);
lean_dec(v_binderName_753_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_816_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_764_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_764_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
v___jp_756_:
{
lean_object* v___f_762_; lean_object* v___x_763_; 
v___f_762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_762_, 0, v_body_755_);
lean_closure_set(v___f_762_, 1, v_eqs_729_);
lean_closure_set(v___f_762_, 2, v_args_730_);
lean_closure_set(v___f_762_, 3, v_arg_757_);
lean_closure_set(v___f_762_, 4, v_mask_731_);
lean_closure_set(v___f_762_, 5, v_i_732_);
lean_closure_set(v___f_762_, 6, v_altType_725_);
lean_closure_set(v___f_762_, 7, v_numDiscrEqs_726_);
lean_closure_set(v___f_762_, 8, v_k_727_);
lean_closure_set(v___f_762_, 9, v_ys_728_);
v___x_763_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_753_, v_binderType_754_, v___f_762_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_a_740_);
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
v___x_824_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_825_ = l_Nat_reprFast(v_numDiscrEqs_726_);
v___x_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
v___x_827_ = l_Lean_MessageData_ofFormat(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_824_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_indentExpr(v_altType_725_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_832_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_833_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_i_732_);
lean_dec_ref(v_mask_731_);
lean_dec_ref(v_args_730_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v_ys_728_);
lean_dec_ref(v_k_727_);
lean_dec(v_numDiscrEqs_726_);
lean_dec_ref(v_altType_725_);
v_a_834_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_739_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_739_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object* v_body_842_, lean_object* v_eqs_843_, lean_object* v_args_844_, lean_object* v_arg_845_, lean_object* v_mask_846_, lean_object* v_i_847_, lean_object* v_altType_848_, lean_object* v_numDiscrEqs_849_, lean_object* v_k_850_, lean_object* v_ys_851_, lean_object* v_eq_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_858_ = lean_expr_instantiate1(v_body_842_, v_eq_852_);
v___x_859_ = lean_array_push(v_eqs_843_, v_eq_852_);
v___x_860_ = lean_array_push(v_args_844_, v_arg_845_);
v___x_861_ = 0;
v___x_862_ = lean_box(v___x_861_);
v___x_863_ = lean_array_push(v_mask_846_, v___x_862_);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_i_847_, v___x_864_);
v___x_866_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_848_, v_numDiscrEqs_849_, v_k_850_, v_ys_851_, v___x_859_, v___x_860_, v___x_863_, v___x_865_, v___x_858_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object* v_altType_867_, lean_object* v_numDiscrEqs_868_, lean_object* v_k_869_, lean_object* v_ys_870_, lean_object* v_eqs_871_, lean_object* v_args_872_, lean_object* v_mask_873_, lean_object* v_i_874_, lean_object* v_type_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_867_, v_numDiscrEqs_868_, v_k_869_, v_ys_870_, v_eqs_871_, v_args_872_, v_mask_873_, v_i_874_, v_type_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object* v_00_u03b1_882_, lean_object* v_altType_883_, lean_object* v_numDiscrEqs_884_, lean_object* v_k_885_, lean_object* v_ys_886_, lean_object* v_eqs_887_, lean_object* v_args_888_, lean_object* v_mask_889_, lean_object* v_i_890_, lean_object* v_type_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_883_, v_numDiscrEqs_884_, v_k_885_, v_ys_886_, v_eqs_887_, v_args_888_, v_mask_889_, v_i_890_, v_type_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object* v_00_u03b1_898_, lean_object* v_altType_899_, lean_object* v_numDiscrEqs_900_, lean_object* v_k_901_, lean_object* v_ys_902_, lean_object* v_eqs_903_, lean_object* v_args_904_, lean_object* v_mask_905_, lean_object* v_i_906_, lean_object* v_type_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(v_00_u03b1_898_, v_altType_899_, v_numDiscrEqs_900_, v_k_901_, v_ys_902_, v_eqs_903_, v_args_904_, v_mask_905_, v_i_906_, v_type_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object* v_altType_914_, lean_object* v_numDiscrEqs_915_, lean_object* v_k_916_, lean_object* v_ys_917_, lean_object* v_args_918_, lean_object* v_mask_919_, lean_object* v_altType_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_928_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_914_, v_numDiscrEqs_915_, v_k_916_, v_ys_917_, v___x_927_, v_args_918_, v_mask_919_, v___x_926_, v_altType_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object* v_altType_929_, lean_object* v_numDiscrEqs_930_, lean_object* v_k_931_, lean_object* v_ys_932_, lean_object* v_args_933_, lean_object* v_mask_934_, lean_object* v_altType_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_929_, v_numDiscrEqs_930_, v_k_931_, v_ys_932_, v_args_933_, v_mask_934_, v_altType_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object* v_altType_942_, lean_object* v_altInfo_943_, lean_object* v_numDiscrEqs_944_, lean_object* v_k_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___f_951_; lean_object* v___x_952_; 
lean_inc_ref(v_altType_942_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_951_, 0, v_altType_942_);
lean_closure_set(v___f_951_, 1, v_numDiscrEqs_944_);
lean_closure_set(v___f_951_, 2, v_k_945_);
v___x_952_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_942_, v_altInfo_943_, v___f_951_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object* v_altType_953_, lean_object* v_altInfo_954_, lean_object* v_numDiscrEqs_955_, lean_object* v_k_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_953_, v_altInfo_954_, v_numDiscrEqs_955_, v_k_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object* v_00_u03b1_963_, lean_object* v_altType_964_, lean_object* v_altInfo_965_, lean_object* v_numDiscrEqs_966_, lean_object* v_k_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_964_, v_altInfo_965_, v_numDiscrEqs_966_, v_k_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object* v_00_u03b1_974_, lean_object* v_altType_975_, lean_object* v_altInfo_976_, lean_object* v_numDiscrEqs_977_, lean_object* v_k_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_Match_forallAltTelescope(v_00_u03b1_974_, v_altType_975_, v_altInfo_976_, v_numDiscrEqs_977_, v_k_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_984_;
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
