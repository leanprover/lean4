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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_dec_ref(v___x_3_);
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
lean_dec_ref(v___x_15_);
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
lean_object* v___f_29_; lean_object* v___x_2403__overap_30_; lean_object* v___x_31_; 
v___f_29_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_2403__overap_30_ = lean_panic_fn(v___f_29_, v_msg_23_);
v___x_31_ = lean_apply_5(v___x_2403__overap_30_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, lean_box(0));
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___boxed(lean_object* v_msg_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v_msg_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
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
lean_object* v___x_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v_mctx_86_; lean_object* v_lctx_87_; lean_object* v_options_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_env_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_83_);
v___x_85_ = lean_st_ref_get(v___y_79_);
v_mctx_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_mctx_86_);
lean_dec(v___x_85_);
v_lctx_87_ = lean_ctor_get(v___y_78_, 2);
v_options_88_ = lean_ctor_get(v___y_80_, 2);
lean_inc_ref(v_options_88_);
lean_inc_ref(v_lctx_87_);
v___x_89_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_89_, 0, v_env_84_);
lean_ctor_set(v___x_89_, 1, v_mctx_86_);
lean_ctor_set(v___x_89_, 2, v_lctx_87_);
lean_ctor_set(v___x_89_, 3, v_options_88_);
v___x_90_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_msgData_77_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(lean_object* v_msgData_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_ref_105_ = lean_ctor_get(v___y_102_, 5);
v___x_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
lean_inc(v_ref_105_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v_ref_105_);
lean_ctor_set(v___x_111_, 1, v_a_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 1);
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(lean_object* v_k_123_, lean_object* v_b_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_6(v_k_123_, v_b_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_131_, lean_object* v_b_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_131_, v_b_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(lean_object* v_name_139_, uint8_t v_bi_140_, lean_object* v_type_141_, lean_object* v_k_142_, uint8_t v_kind_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_149_, 0, v_k_142_);
v___x_150_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_139_, v_bi_140_, v_type_141_, v___f_149_, v_kind_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_150_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_150_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(lean_object* v_name_167_, lean_object* v_bi_168_, lean_object* v_type_169_, lean_object* v_k_170_, lean_object* v_kind_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
uint8_t v_bi_boxed_177_; uint8_t v_kind_boxed_178_; lean_object* v_res_179_; 
v_bi_boxed_177_ = lean_unbox(v_bi_168_);
v_kind_boxed_178_ = lean_unbox(v_kind_171_);
v_res_179_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_167_, v_bi_boxed_177_, v_type_169_, v_k_170_, v_kind_boxed_178_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(lean_object* v_name_180_, lean_object* v_type_181_, lean_object* v_k_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = 0;
v___x_189_ = 0;
v___x_190_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_180_, v___x_188_, v_type_181_, v_k_182_, v___x_189_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(lean_object* v_name_191_, lean_object* v_type_192_, lean_object* v_k_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_191_, v_type_192_, v_k_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(lean_object* v_fst_200_, lean_object* v_snd_201_, size_t v_sz_202_, size_t v_i_203_, lean_object* v_bs_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_usize_dec_lt(v_i_203_, v_sz_202_);
if (v___x_205_ == 0)
{
lean_dec_ref(v_snd_201_);
return v_bs_204_;
}
else
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; lean_object* v___y_210_; uint8_t v___x_215_; 
v_v_206_ = lean_array_uget(v_bs_204_, v_i_203_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_204_, v_i_203_, v___x_207_);
v___x_215_ = lean_expr_eqv(v_v_206_, v_fst_200_);
if (v___x_215_ == 0)
{
v___y_210_ = v_v_206_;
goto v___jp_209_;
}
else
{
lean_dec(v_v_206_);
lean_inc_ref(v_snd_201_);
v___y_210_ = v_snd_201_;
goto v___jp_209_;
}
v___jp_209_:
{
size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_add(v_i_203_, v___x_211_);
v___x_213_ = lean_array_uset(v_bs_x27_208_, v_i_203_, v___y_210_);
v_i_203_ = v___x_212_;
v_bs_204_ = v___x_213_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(lean_object* v_fst_216_, lean_object* v_snd_217_, lean_object* v_sz_218_, lean_object* v_i_219_, lean_object* v_bs_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_218_);
lean_dec(v_sz_218_);
v_i_boxed_222_ = lean_unbox_usize(v_i_219_);
lean_dec(v_i_219_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_216_, v_snd_217_, v_sz_boxed_221_, v_i_boxed_222_, v_bs_220_);
lean_dec_ref(v_fst_216_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(lean_object* v_a_224_, lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
v___x_230_ = lean_expr_eqv(v_a_224_, v___x_229_);
if (v___x_230_ == 0)
{
size_t v___x_231_; size_t v___x_232_; 
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_226_, v___x_231_);
v_i_226_ = v___x_232_;
goto _start;
}
else
{
return v___x_230_;
}
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(lean_object* v_a_235_, lean_object* v_as_236_, lean_object* v_i_237_, lean_object* v_stop_238_){
_start:
{
size_t v_i_boxed_239_; size_t v_stop_boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_i_boxed_239_ = lean_unbox_usize(v_i_237_);
lean_dec(v_i_237_);
v_stop_boxed_240_ = lean_unbox_usize(v_stop_238_);
lean_dec(v_stop_238_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_235_, v_as_236_, v_i_boxed_239_, v_stop_boxed_240_);
lean_dec_ref(v_as_236_);
lean_dec_ref(v_a_235_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(lean_object* v_as_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_array_get_size(v_as_243_);
v___x_247_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
return v___x_247_;
}
else
{
if (v___x_247_ == 0)
{
return v___x_247_;
}
else
{
size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v___x_248_ = ((size_t)0ULL);
v___x_249_ = lean_usize_of_nat(v___x_246_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_244_, v_as_243_, v___x_248_, v___x_249_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(lean_object* v_as_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_251_, v_a_252_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_as_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(lean_object* v_altType_261_, lean_object* v_altInfo_262_, lean_object* v_k_263_, lean_object* v_ys_264_, lean_object* v_args_265_, lean_object* v_mask_266_, lean_object* v_i_267_, lean_object* v_type_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_261_, v_altInfo_262_, v_k_263_, v_ys_264_, v_args_265_, v_mask_266_, v_i_267_, v_type_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
return v_res_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_279_ = lean_unsigned_to_nat(47u);
v___x_280_ = lean_unsigned_to_nat(68u);
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_283_ = l_mkPanicMessageWithDecl(v___x_282_, v___x_281_, v___x_280_, v___x_279_, v___x_278_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_285_ = lean_unsigned_to_nat(48u);
v___x_286_ = lean_unsigned_to_nat(66u);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_289_ = l_mkPanicMessageWithDecl(v___x_288_, v___x_287_, v___x_286_, v___x_285_, v___x_284_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object* v_a_290_, lean_object* v_body_291_, lean_object* v_ys_292_, lean_object* v_args_293_, lean_object* v_mask_294_, uint8_t v___x_295_, lean_object* v_i_296_, lean_object* v_altType_297_, lean_object* v_altInfo_298_, lean_object* v_k_299_, lean_object* v_y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
v___x_306_ = l_Lean_Meta_matchEq_x3f(v_a_290_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
v___x_308_ = lean_expr_instantiate1(v_body_291_, v_y_300_);
if (lean_obj_tag(v_a_307_) == 1)
{
lean_object* v_val_321_; lean_object* v_snd_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___y_326_; uint8_t v___x_381_; 
v_val_321_ = lean_ctor_get(v_a_307_, 0);
lean_inc(v_val_321_);
lean_dec_ref(v_a_307_);
v_snd_322_ = lean_ctor_get(v_val_321_, 1);
lean_inc(v_snd_322_);
lean_dec(v_val_321_);
v_fst_323_ = lean_ctor_get(v_snd_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v_snd_322_, 1);
lean_inc(v_snd_324_);
lean_dec(v_snd_322_);
v___x_381_ = l_Lean_Expr_isFVar(v_fst_323_);
if (v___x_381_ == 0)
{
v___y_326_ = v___x_381_;
goto v___jp_325_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_292_, v_fst_323_);
v___y_326_ = v___x_382_;
goto v___jp_325_;
}
v___jp_325_:
{
if (v___y_326_ == 0)
{
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_293_, v_fst_323_);
if (v___x_327_ == 0)
{
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
else
{
uint8_t v___x_328_; 
lean_inc_ref(v_y_300_);
v___x_328_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_308_, v_y_300_);
if (v___x_328_ == 0)
{
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_292_, v_fst_323_);
if (lean_obj_tag(v___x_329_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_331_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___x_329_);
v___x_331_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_293_, v_fst_323_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref(v___x_331_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v_snd_324_);
v___x_333_ = l_Lean_Meta_mkEqRefl(v_snd_324_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; size_t v_sz_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; size_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
v_sz_335_ = lean_array_size(v_args_293_);
v___x_336_ = l_Array_eraseIdx___redArg(v_ys_292_, v_val_330_);
v___x_337_ = 0;
v___x_338_ = lean_box(v___x_337_);
v___x_339_ = lean_array_set(v_mask_294_, v_val_332_, v___x_338_);
lean_dec(v_val_332_);
v___x_340_ = ((size_t)0ULL);
lean_inc(v_snd_324_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_323_, v_snd_324_, v_sz_335_, v___x_340_, v_args_293_);
lean_inc(v_fst_323_);
v___x_342_ = l_Lean_Expr_replaceFVar(v___x_308_, v_fst_323_, v_snd_324_);
lean_dec_ref(v___x_308_);
v___x_343_ = l_Lean_Expr_fvarId_x21(v_fst_323_);
lean_dec(v_fst_323_);
v___x_344_ = l_Lean_Expr_fvarId_x21(v_y_300_);
lean_dec_ref(v_y_300_);
lean_inc(v_a_334_);
v___x_345_ = lean_array_push(v___x_341_, v_a_334_);
v___x_346_ = lean_box(v___x_337_);
v___x_347_ = lean_array_push(v___x_339_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_i_296_, v___x_348_);
v___x_350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed), 13, 8);
lean_closure_set(v___x_350_, 0, v_altType_297_);
lean_closure_set(v___x_350_, 1, v_altInfo_298_);
lean_closure_set(v___x_350_, 2, v_k_299_);
lean_closure_set(v___x_350_, 3, v___x_336_);
lean_closure_set(v___x_350_, 4, v___x_345_);
lean_closure_set(v___x_350_, 5, v___x_347_);
lean_closure_set(v___x_350_, 6, v___x_349_);
lean_closure_set(v___x_350_, 7, v___x_342_);
v___x_351_ = lean_alloc_closure((void*)(l_Lean_Meta_withReplaceFVarId___boxed), 9, 4);
lean_closure_set(v___x_351_, 0, lean_box(0));
lean_closure_set(v___x_351_, 1, v___x_344_);
lean_closure_set(v___x_351_, 2, v_a_334_);
lean_closure_set(v___x_351_, 3, v___x_350_);
v___x_352_ = l_Lean_Meta_withReplaceFVarId___redArg(v___x_343_, v_snd_324_, v___x_351_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_352_;
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_val_332_);
lean_dec(v_val_330_);
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
lean_dec_ref(v___x_308_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_y_300_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_353_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_333_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_333_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v___x_331_);
lean_dec(v_val_330_);
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
v___x_362_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_361_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref(v___x_362_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v___x_308_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_y_300_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
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
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_329_);
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
v___x_372_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_371_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref(v___x_372_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___x_308_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_y_300_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
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
}
}
}
}
else
{
lean_dec(v_a_307_);
v___y_310_ = v___y_301_;
v___y_311_ = v___y_302_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_inc_ref(v_y_300_);
v___x_314_ = lean_array_push(v_ys_292_, v_y_300_);
v___x_315_ = lean_array_push(v_args_293_, v_y_300_);
v___x_316_ = lean_box(v___x_295_);
v___x_317_ = lean_array_push(v_mask_294_, v___x_316_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_i_296_, v___x_318_);
v___x_320_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_297_, v_altInfo_298_, v_k_299_, v___x_314_, v___x_315_, v___x_317_, v___x_319_, v___x_308_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
return v___x_320_;
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_y_300_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_altInfo_298_);
lean_dec_ref(v_altType_297_);
lean_dec_ref(v_mask_294_);
lean_dec_ref(v_args_293_);
lean_dec_ref(v_ys_292_);
v_a_383_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_306_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_306_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object* v_a_391_, lean_object* v_body_392_, lean_object* v_ys_393_, lean_object* v_args_394_, lean_object* v_mask_395_, lean_object* v___x_396_, lean_object* v_i_397_, lean_object* v_altType_398_, lean_object* v_altInfo_399_, lean_object* v_k_400_, lean_object* v_y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_4488__boxed_407_; lean_object* v_res_408_; 
v___x_4488__boxed_407_ = lean_unbox(v___x_396_);
v_res_408_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_a_391_, v_body_392_, v_ys_393_, v_args_394_, v_mask_395_, v___x_4488__boxed_407_, v_i_397_, v_altType_398_, v_altInfo_399_, v_k_400_, v_y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v_i_397_);
lean_dec_ref(v_body_392_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(lean_object* v_altType_409_, lean_object* v_altInfo_410_, lean_object* v_k_411_, lean_object* v_ys_412_, lean_object* v_args_413_, lean_object* v_mask_414_, lean_object* v_i_415_, lean_object* v_type_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; 
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
v___x_422_ = l_Lean_Meta_whnfForall(v_type_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v_numFields_424_; uint8_t v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
v_numFields_424_ = lean_ctor_get(v_altInfo_410_, 0);
v___x_425_ = lean_nat_dec_lt(v_i_415_, v_numFields_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec(v_i_415_);
lean_dec_ref(v_altInfo_410_);
lean_dec_ref(v_altType_409_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
v___x_426_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_423_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
v___x_428_ = lean_apply_9(v_k_411_, v_ys_412_, v_args_413_, v_mask_414_, v_a_427_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, lean_box(0));
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec_ref(v_mask_414_);
lean_dec_ref(v_args_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_k_411_);
v_a_429_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_426_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_426_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_423_) == 7)
{
lean_object* v_binderName_437_; lean_object* v_binderType_438_; lean_object* v_body_439_; lean_object* v___x_440_; 
v_binderName_437_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_binderName_437_);
v_binderType_438_ = lean_ctor_get(v_a_423_, 1);
lean_inc_ref(v_binderType_438_);
v_body_439_ = lean_ctor_get(v_a_423_, 2);
lean_inc_ref(v_body_439_);
lean_dec_ref(v_a_423_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
v___x_440_ = l_Lean_Meta_Match_unfoldNamedPattern(v_binderType_438_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v___x_442_ = lean_box(v___x_425_);
lean_inc(v_a_441_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_443_, 0, v_a_441_);
lean_closure_set(v___f_443_, 1, v_body_439_);
lean_closure_set(v___f_443_, 2, v_ys_412_);
lean_closure_set(v___f_443_, 3, v_args_413_);
lean_closure_set(v___f_443_, 4, v_mask_414_);
lean_closure_set(v___f_443_, 5, v___x_442_);
lean_closure_set(v___f_443_, 6, v_i_415_);
lean_closure_set(v___f_443_, 7, v_altType_409_);
lean_closure_set(v___f_443_, 8, v_altInfo_410_);
lean_closure_set(v___f_443_, 9, v_k_411_);
v___x_444_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_437_, v_a_441_, v___f_443_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v_body_439_);
lean_dec(v_binderName_437_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_i_415_);
lean_dec_ref(v_mask_414_);
lean_dec_ref(v_args_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_k_411_);
lean_dec_ref(v_altInfo_410_);
lean_dec_ref(v_altType_409_);
v_a_445_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_440_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_440_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc(v_numFields_424_);
lean_dec(v_a_423_);
lean_dec(v_i_415_);
lean_dec_ref(v_mask_414_);
lean_dec_ref(v_args_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_k_411_);
lean_dec_ref(v_altInfo_410_);
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_454_ = l_Nat_reprFast(v_numFields_424_);
v___x_455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = l_Lean_MessageData_ofFormat(v___x_455_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_453_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_indentExpr(v_altType_409_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_461_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
return v___x_462_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_i_415_);
lean_dec_ref(v_mask_414_);
lean_dec_ref(v_args_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_k_411_);
lean_dec_ref(v_altInfo_410_);
lean_dec_ref(v_altType_409_);
v_a_463_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_422_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_422_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(lean_object* v_00_u03b1_471_, lean_object* v_altType_472_, lean_object* v_altInfo_473_, lean_object* v_k_474_, lean_object* v_ys_475_, lean_object* v_args_476_, lean_object* v_mask_477_, lean_object* v_i_478_, lean_object* v_type_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_472_, v_altInfo_473_, v_k_474_, v_ys_475_, v_args_476_, v_mask_477_, v_i_478_, v_type_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(lean_object* v_00_u03b1_486_, lean_object* v_altType_487_, lean_object* v_altInfo_488_, lean_object* v_k_489_, lean_object* v_ys_490_, lean_object* v_args_491_, lean_object* v_mask_492_, lean_object* v_i_493_, lean_object* v_type_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(v_00_u03b1_486_, v_altType_487_, v_altInfo_488_, v_k_489_, v_ys_490_, v_args_491_, v_mask_492_, v_i_493_, v_type_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(lean_object* v_00_u03b1_501_, lean_object* v_name_502_, uint8_t v_bi_503_, lean_object* v_type_504_, lean_object* v_k_505_, uint8_t v_kind_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_502_, v_bi_503_, v_type_504_, v_k_505_, v_kind_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_513_, lean_object* v_name_514_, lean_object* v_bi_515_, lean_object* v_type_516_, lean_object* v_k_517_, lean_object* v_kind_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v_bi_boxed_524_; uint8_t v_kind_boxed_525_; lean_object* v_res_526_; 
v_bi_boxed_524_ = lean_unbox(v_bi_515_);
v_kind_boxed_525_ = lean_unbox(v_kind_518_);
v_res_526_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(v_00_u03b1_513_, v_name_514_, v_bi_boxed_524_, v_type_516_, v_k_517_, v_kind_boxed_525_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(lean_object* v_00_u03b1_527_, lean_object* v_name_528_, lean_object* v_type_529_, lean_object* v_k_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_528_, v_type_529_, v_k_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(lean_object* v_00_u03b1_537_, lean_object* v_name_538_, lean_object* v_type_539_, lean_object* v_k_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(v_00_u03b1_537_, v_name_538_, v_type_539_, v_k_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(lean_object* v_00_u03b1_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(lean_object* v_00_u03b1_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(v_00_u03b1_555_, v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___f_569_; lean_object* v___x_504__overap_570_; lean_object* v___x_571_; 
v___f_569_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_504__overap_570_ = lean_panic_fn(v___f_569_, v_msg_563_);
v___x_571_ = lean_apply_5(v___x_504__overap_570_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, lean_box(0));
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(lean_object* v_00_u03b1_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(lean_object* v_00_u03b1_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(v_00_u03b1_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1));
v___x_598_ = lean_unsigned_to_nat(2u);
v___x_599_ = lean_unsigned_to_nat(45u);
v___x_600_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0));
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_602_ = l_mkPanicMessageWithDecl(v___x_601_, v___x_600_, v___x_599_, v___x_598_, v___x_597_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
v___x_611_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6));
v___x_612_ = l_Lean_mkConst(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_array_push(v___x_615_, v___x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object* v_altType_622_, lean_object* v_altInfo_623_, lean_object* v_k_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_numOverlaps_630_; uint8_t v_hasUnitThunk_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_numOverlaps_630_ = lean_ctor_get(v_altInfo_623_, 1);
v_hasUnitThunk_631_ = lean_ctor_get_uint8(v_altInfo_623_, sizeof(void*)*2);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_eq(v_numOverlaps_630_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_k_624_);
lean_dec_ref(v_altInfo_623_);
lean_dec_ref(v_altType_622_);
v___x_634_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2);
v___x_635_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(v___x_634_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_635_;
}
else
{
if (v_hasUnitThunk_631_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
lean_inc_ref(v_altType_622_);
v___x_637_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_622_, v_altInfo_623_, v_k_624_, v___x_636_, v___x_636_, v___x_636_, v___x_632_, v_altType_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_altInfo_623_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
v___x_638_ = l_Lean_Meta_whnfForall(v_altType_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
v___x_640_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_639_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8, &l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once, _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
v___x_643_ = l_Lean_Meta_instantiateForall(v_a_641_, v___x_642_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_646_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9));
v___x_647_ = lean_apply_9(v_k_624_, v___x_645_, v___x_642_, v___x_646_, v_a_644_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, lean_box(0));
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_k_624_);
v_a_648_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_643_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_643_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_k_624_);
v_a_656_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_640_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_640_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_k_624_);
v_a_664_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_638_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_638_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(lean_object* v_altType_672_, lean_object* v_altInfo_673_, lean_object* v_k_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_672_, v_altInfo_673_, v_k_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope(lean_object* v_00_u03b1_681_, lean_object* v_altType_682_, lean_object* v_altInfo_683_, lean_object* v_k_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_682_, v_altInfo_683_, v_k_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___boxed(lean_object* v_00_u03b1_691_, lean_object* v_altType_692_, lean_object* v_altInfo_693_, lean_object* v_k_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Match_forallAltVarsTelescope(v_00_u03b1_691_, v_altType_692_, v_altInfo_693_, v_k_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(lean_object* v_body_701_, lean_object* v_eqs_702_, lean_object* v_args_703_, lean_object* v_arg_704_, lean_object* v_mask_705_, lean_object* v_i_706_, lean_object* v_altType_707_, lean_object* v_numDiscrEqs_708_, lean_object* v_k_709_, lean_object* v_ys_710_, lean_object* v_eq_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_701_, v_eqs_702_, v_args_703_, v_arg_704_, v_mask_705_, v_i_706_, v_altType_707_, v_numDiscrEqs_708_, v_k_709_, v_ys_710_, v_eq_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v_i_706_);
lean_dec_ref(v_body_701_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0));
v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2));
v___x_723_ = l_Lean_stringToMessageData(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(lean_object* v_altType_724_, lean_object* v_numDiscrEqs_725_, lean_object* v_k_726_, lean_object* v_ys_727_, lean_object* v_eqs_728_, lean_object* v_args_729_, lean_object* v_mask_730_, lean_object* v_i_731_, lean_object* v_type_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
v___x_738_ = l_Lean_Meta_whnfForall(v_type_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = lean_nat_dec_lt(v_i_731_, v_numDiscrEqs_725_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_i_731_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
v___x_741_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_739_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___x_741_);
v___x_743_ = lean_apply_10(v_k_726_, v_ys_727_, v_eqs_728_, v_args_729_, v_mask_730_, v_a_742_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, lean_box(0));
return v___x_743_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
v_a_744_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_741_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_739_) == 7)
{
lean_object* v_binderName_752_; lean_object* v_binderType_753_; lean_object* v_body_754_; lean_object* v_arg_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___x_763_; 
v_binderName_752_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_binderName_752_);
v_binderType_753_ = lean_ctor_get(v_a_739_, 1);
lean_inc_ref(v_binderType_753_);
v_body_754_ = lean_ctor_get(v_a_739_, 2);
lean_inc_ref(v_body_754_);
lean_dec_ref(v_a_739_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc_ref(v_binderType_753_);
v___x_763_ = l_Lean_Meta_matchEq_x3f(v_binderType_753_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v_a_764_) == 1)
{
lean_object* v_val_765_; lean_object* v_snd_766_; lean_object* v_snd_767_; lean_object* v___x_768_; 
v_val_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_a_764_);
v_snd_766_ = lean_ctor_get(v_val_765_, 1);
lean_inc(v_snd_766_);
lean_dec(v_val_765_);
v_snd_767_ = lean_ctor_get(v_snd_766_, 1);
lean_inc(v_snd_767_);
lean_dec(v_snd_766_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
v___x_768_ = l_Lean_Meta_mkEqRefl(v_snd_767_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v_arg_756_ = v_a_769_;
v___y_757_ = v_a_733_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
goto v___jp_755_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_body_754_);
lean_dec_ref(v_binderType_753_);
lean_dec(v_binderName_752_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_770_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_768_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_a_764_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc_ref(v_binderType_753_);
v___x_778_ = l_Lean_Meta_matchHEq_x3f(v_binderType_753_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
if (lean_obj_tag(v_a_779_) == 1)
{
lean_object* v_val_780_; lean_object* v_snd_781_; lean_object* v_snd_782_; lean_object* v_snd_783_; lean_object* v___x_784_; 
v_val_780_ = lean_ctor_get(v_a_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v_a_779_);
v_snd_781_ = lean_ctor_get(v_val_780_, 1);
lean_inc(v_snd_781_);
lean_dec(v_val_780_);
v_snd_782_ = lean_ctor_get(v_snd_781_, 1);
lean_inc(v_snd_782_);
lean_dec(v_snd_781_);
v_snd_783_ = lean_ctor_get(v_snd_782_, 1);
lean_inc(v_snd_783_);
lean_dec(v_snd_782_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
v___x_784_ = l_Lean_Meta_mkHEqRefl(v_snd_783_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v_arg_756_ = v_a_785_;
v___y_757_ = v_a_733_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
goto v___jp_755_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_body_754_);
lean_dec_ref(v_binderType_753_);
lean_dec(v_binderName_752_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_786_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_784_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_a_779_);
v___x_794_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
lean_inc_ref(v_altType_724_);
v___x_795_ = l_Lean_indentExpr(v_altType_724_);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_796_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v_arg_756_ = v_a_798_;
v___y_757_ = v_a_733_;
v___y_758_ = v_a_734_;
v___y_759_ = v_a_735_;
v___y_760_ = v_a_736_;
goto v___jp_755_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_body_754_);
lean_dec_ref(v_binderType_753_);
lean_dec(v_binderName_752_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_799_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_body_754_);
lean_dec_ref(v_binderType_753_);
lean_dec(v_binderName_752_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_807_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_778_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_778_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_body_754_);
lean_dec_ref(v_binderType_753_);
lean_dec(v_binderName_752_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_815_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_763_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_763_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
v___jp_755_:
{
lean_object* v___f_761_; lean_object* v___x_762_; 
v___f_761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_761_, 0, v_body_754_);
lean_closure_set(v___f_761_, 1, v_eqs_728_);
lean_closure_set(v___f_761_, 2, v_args_729_);
lean_closure_set(v___f_761_, 3, v_arg_756_);
lean_closure_set(v___f_761_, 4, v_mask_730_);
lean_closure_set(v___f_761_, 5, v_i_731_);
lean_closure_set(v___f_761_, 6, v_altType_724_);
lean_closure_set(v___f_761_, 7, v_numDiscrEqs_725_);
lean_closure_set(v___f_761_, 8, v_k_726_);
lean_closure_set(v___f_761_, 9, v_ys_727_);
v___x_762_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_752_, v_binderType_753_, v___f_761_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
return v___x_762_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_a_739_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
v___x_823_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_824_ = l_Nat_reprFast(v_numDiscrEqs_725_);
v___x_825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = l_Lean_MessageData_ofFormat(v___x_825_);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_823_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_indentExpr(v_altType_724_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_831_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v___x_832_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_i_731_);
lean_dec_ref(v_mask_730_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v_eqs_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_k_726_);
lean_dec(v_numDiscrEqs_725_);
lean_dec_ref(v_altType_724_);
v_a_833_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_738_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_738_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object* v_body_841_, lean_object* v_eqs_842_, lean_object* v_args_843_, lean_object* v_arg_844_, lean_object* v_mask_845_, lean_object* v_i_846_, lean_object* v_altType_847_, lean_object* v_numDiscrEqs_848_, lean_object* v_k_849_, lean_object* v_ys_850_, lean_object* v_eq_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_857_ = lean_expr_instantiate1(v_body_841_, v_eq_851_);
v___x_858_ = lean_array_push(v_eqs_842_, v_eq_851_);
v___x_859_ = lean_array_push(v_args_843_, v_arg_844_);
v___x_860_ = 0;
v___x_861_ = lean_box(v___x_860_);
v___x_862_ = lean_array_push(v_mask_845_, v___x_861_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_i_846_, v___x_863_);
v___x_865_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_847_, v_numDiscrEqs_848_, v_k_849_, v_ys_850_, v___x_858_, v___x_859_, v___x_862_, v___x_864_, v___x_857_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object* v_altType_866_, lean_object* v_numDiscrEqs_867_, lean_object* v_k_868_, lean_object* v_ys_869_, lean_object* v_eqs_870_, lean_object* v_args_871_, lean_object* v_mask_872_, lean_object* v_i_873_, lean_object* v_type_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_866_, v_numDiscrEqs_867_, v_k_868_, v_ys_869_, v_eqs_870_, v_args_871_, v_mask_872_, v_i_873_, v_type_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object* v_00_u03b1_881_, lean_object* v_altType_882_, lean_object* v_numDiscrEqs_883_, lean_object* v_k_884_, lean_object* v_ys_885_, lean_object* v_eqs_886_, lean_object* v_args_887_, lean_object* v_mask_888_, lean_object* v_i_889_, lean_object* v_type_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_882_, v_numDiscrEqs_883_, v_k_884_, v_ys_885_, v_eqs_886_, v_args_887_, v_mask_888_, v_i_889_, v_type_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object* v_00_u03b1_897_, lean_object* v_altType_898_, lean_object* v_numDiscrEqs_899_, lean_object* v_k_900_, lean_object* v_ys_901_, lean_object* v_eqs_902_, lean_object* v_args_903_, lean_object* v_mask_904_, lean_object* v_i_905_, lean_object* v_type_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(v_00_u03b1_897_, v_altType_898_, v_numDiscrEqs_899_, v_k_900_, v_ys_901_, v_eqs_902_, v_args_903_, v_mask_904_, v_i_905_, v_type_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object* v_altType_913_, lean_object* v_numDiscrEqs_914_, lean_object* v_k_915_, lean_object* v_ys_916_, lean_object* v_args_917_, lean_object* v_mask_918_, lean_object* v_altType_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_927_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_913_, v_numDiscrEqs_914_, v_k_915_, v_ys_916_, v___x_926_, v_args_917_, v_mask_918_, v___x_925_, v_altType_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object* v_altType_928_, lean_object* v_numDiscrEqs_929_, lean_object* v_k_930_, lean_object* v_ys_931_, lean_object* v_args_932_, lean_object* v_mask_933_, lean_object* v_altType_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_928_, v_numDiscrEqs_929_, v_k_930_, v_ys_931_, v_args_932_, v_mask_933_, v_altType_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object* v_altType_941_, lean_object* v_altInfo_942_, lean_object* v_numDiscrEqs_943_, lean_object* v_k_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___f_950_; lean_object* v___x_951_; 
lean_inc_ref(v_altType_941_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_950_, 0, v_altType_941_);
lean_closure_set(v___f_950_, 1, v_numDiscrEqs_943_);
lean_closure_set(v___f_950_, 2, v_k_944_);
v___x_951_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_941_, v_altInfo_942_, v___f_950_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object* v_altType_952_, lean_object* v_altInfo_953_, lean_object* v_numDiscrEqs_954_, lean_object* v_k_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_952_, v_altInfo_953_, v_numDiscrEqs_954_, v_k_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object* v_00_u03b1_962_, lean_object* v_altType_963_, lean_object* v_altInfo_964_, lean_object* v_numDiscrEqs_965_, lean_object* v_k_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_963_, v_altInfo_964_, v_numDiscrEqs_965_, v_k_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object* v_00_u03b1_973_, lean_object* v_altType_974_, lean_object* v_altInfo_975_, lean_object* v_numDiscrEqs_976_, lean_object* v_k_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Meta_Match_forallAltTelescope(v_00_u03b1_973_, v_altType_974_, v_altInfo_975_, v_numDiscrEqs_976_, v_k_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v_res_983_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
