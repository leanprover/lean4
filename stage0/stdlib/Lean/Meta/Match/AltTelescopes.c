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
uint8_t l_Lean_Expr_isFVar(lean_object*);
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
lean_object* v___f_29_; lean_object* v___x_2007__overap_30_; lean_object* v___x_31_; 
v___f_29_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0));
v___x_2007__overap_30_ = lean_panic_fn_borrowed(v___f_29_, v_msg_23_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
lean_inc(v___y_25_);
lean_inc_ref(v___y_24_);
v___x_31_ = lean_apply_5(v___x_2007__overap_30_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, lean_box(0));
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
lean_object* v___x_83_; lean_object* v_env_84_; uint8_t v___x_85_; lean_object* v_env_86_; lean_object* v___x_87_; lean_object* v_toCold_88_; lean_object* v_mctx_89_; lean_object* v_lctx_90_; lean_object* v_options_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_env_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_83_);
v___x_85_ = 0;
v_env_86_ = l_Lean_Environment_setRecordingDeps(v_env_84_, v___x_85_);
v___x_87_ = lean_st_ref_get(v___y_79_);
v_toCold_88_ = lean_ctor_get(v___y_80_, 0);
v_mctx_89_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_mctx_89_);
lean_dec(v___x_87_);
v_lctx_90_ = lean_ctor_get(v___y_78_, 2);
v_options_91_ = lean_ctor_get(v_toCold_88_, 2);
lean_inc_ref(v_options_91_);
lean_inc_ref(v_lctx_90_);
v___x_92_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_92_, 0, v_env_86_);
lean_ctor_set(v___x_92_, 1, v_mctx_89_);
lean_ctor_set(v___x_92_, 2, v_lctx_90_);
lean_ctor_set(v___x_92_, 3, v_options_91_);
v___x_93_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_msgData_77_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(lean_object* v_msg_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_ref_108_; lean_object* v___x_109_; lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_ref_108_ = lean_ctor_get(v___y_105_, 2);
v___x_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msg_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_inc(v_ref_108_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_ref_108_);
lean_ctor_set(v___x_114_, 1, v_a_110_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 1);
lean_ctor_set(v___x_112_, 0, v___x_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(lean_object* v_k_126_, lean_object* v_b_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_133_ = lean_apply_6(v_k_126_, v_b_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_134_, lean_object* v_b_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_134_, v_b_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(lean_object* v_name_142_, uint8_t v_bi_143_, lean_object* v_type_144_, lean_object* v_k_145_, uint8_t v_kind_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; 
v___f_152_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_152_, 0, v_k_145_);
v___x_153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_142_, v_bi_143_, v_type_144_, v___f_152_, v_kind_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_153_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(lean_object* v_name_170_, lean_object* v_bi_171_, lean_object* v_type_172_, lean_object* v_k_173_, lean_object* v_kind_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
uint8_t v_bi_boxed_180_; uint8_t v_kind_boxed_181_; lean_object* v_res_182_; 
v_bi_boxed_180_ = lean_unbox(v_bi_171_);
v_kind_boxed_181_ = lean_unbox(v_kind_174_);
v_res_182_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_170_, v_bi_boxed_180_, v_type_172_, v_k_173_, v_kind_boxed_181_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(lean_object* v_name_183_, lean_object* v_type_184_, lean_object* v_k_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; 
v___x_191_ = 0;
v___x_192_ = 0;
v___x_193_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_183_, v___x_191_, v_type_184_, v_k_185_, v___x_192_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(lean_object* v_name_194_, lean_object* v_type_195_, lean_object* v_k_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_194_, v_type_195_, v_k_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(lean_object* v_fst_203_, lean_object* v_snd_204_, size_t v_sz_205_, size_t v_i_206_, lean_object* v_bs_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_usize_dec_lt(v_i_206_, v_sz_205_);
if (v___x_208_ == 0)
{
lean_dec_ref(v_snd_204_);
return v_bs_207_;
}
else
{
lean_object* v_v_209_; lean_object* v___x_210_; lean_object* v_bs_x27_211_; lean_object* v___y_213_; uint8_t v___x_218_; 
v_v_209_ = lean_array_uget(v_bs_207_, v_i_206_);
v___x_210_ = lean_unsigned_to_nat(0u);
v_bs_x27_211_ = lean_array_uset(v_bs_207_, v_i_206_, v___x_210_);
v___x_218_ = lean_expr_eqv(v_v_209_, v_fst_203_);
if (v___x_218_ == 0)
{
v___y_213_ = v_v_209_;
goto v___jp_212_;
}
else
{
lean_dec(v_v_209_);
lean_inc_ref(v_snd_204_);
v___y_213_ = v_snd_204_;
goto v___jp_212_;
}
v___jp_212_:
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_add(v_i_206_, v___x_214_);
v___x_216_ = lean_array_uset(v_bs_x27_211_, v_i_206_, v___y_213_);
v_i_206_ = v___x_215_;
v_bs_207_ = v___x_216_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(lean_object* v_fst_219_, lean_object* v_snd_220_, lean_object* v_sz_221_, lean_object* v_i_222_, lean_object* v_bs_223_){
_start:
{
size_t v_sz_boxed_224_; size_t v_i_boxed_225_; lean_object* v_res_226_; 
v_sz_boxed_224_ = lean_unbox_usize(v_sz_221_);
lean_dec(v_sz_221_);
v_i_boxed_225_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_219_, v_snd_220_, v_sz_boxed_224_, v_i_boxed_225_, v_bs_223_);
lean_dec_ref(v_fst_219_);
return v_res_226_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(lean_object* v_a_227_, lean_object* v_as_228_, size_t v_i_229_, size_t v_stop_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_229_, v_stop_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_uget_borrowed(v_as_228_, v_i_229_);
v___x_233_ = lean_expr_eqv(v_a_227_, v___x_232_);
if (v___x_233_ == 0)
{
size_t v___x_234_; size_t v___x_235_; 
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_229_, v___x_234_);
v_i_229_ = v___x_235_;
goto _start;
}
else
{
return v___x_233_;
}
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(lean_object* v_a_238_, lean_object* v_as_239_, lean_object* v_i_240_, lean_object* v_stop_241_){
_start:
{
size_t v_i_boxed_242_; size_t v_stop_boxed_243_; uint8_t v_res_244_; lean_object* v_r_245_; 
v_i_boxed_242_ = lean_unbox_usize(v_i_240_);
lean_dec(v_i_240_);
v_stop_boxed_243_ = lean_unbox_usize(v_stop_241_);
lean_dec(v_stop_241_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_238_, v_as_239_, v_i_boxed_242_, v_stop_boxed_243_);
lean_dec_ref(v_as_239_);
lean_dec_ref(v_a_238_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(lean_object* v_as_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_array_get_size(v_as_246_);
v___x_250_ = lean_nat_dec_lt(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
return v___x_250_;
}
else
{
size_t v___x_251_; size_t v___x_252_; uint8_t v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_249_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_247_, v_as_246_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(lean_object* v_as_254_, lean_object* v_a_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_254_, v_a_255_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_as_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(lean_object* v_altType_264_, lean_object* v_altInfo_265_, lean_object* v_k_266_, lean_object* v_ys_267_, lean_object* v_args_268_, lean_object* v_mask_269_, lean_object* v_i_270_, lean_object* v_type_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_264_, v_altInfo_265_, v_k_266_, v_ys_267_, v_args_268_, v_mask_269_, v_i_270_, v_type_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_282_ = lean_unsigned_to_nat(47u);
v___x_283_ = lean_unsigned_to_nat(68u);
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_286_ = l_mkPanicMessageWithDecl(v___x_285_, v___x_284_, v___x_283_, v___x_282_, v___x_281_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2));
v___x_288_ = lean_unsigned_to_nat(48u);
v___x_289_ = lean_unsigned_to_nat(66u);
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1));
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0));
v___x_292_ = l_mkPanicMessageWithDecl(v___x_291_, v___x_290_, v___x_289_, v___x_288_, v___x_287_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(lean_object* v_body_293_, lean_object* v_ys_294_, lean_object* v_args_295_, lean_object* v_mask_296_, uint8_t v___x_297_, lean_object* v_i_298_, lean_object* v_altType_299_, lean_object* v_altInfo_300_, lean_object* v_k_301_, lean_object* v_a_302_, lean_object* v_y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_318_; 
v___x_309_ = lean_expr_instantiate1(v_body_293_, v_y_303_);
v___x_318_ = l_Lean_Meta_matchEq_x3f(v_a_302_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
if (lean_obj_tag(v_a_319_) == 1)
{
lean_object* v_val_320_; lean_object* v_snd_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; uint8_t v___x_324_; 
v_val_320_ = lean_ctor_get(v_a_319_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v_a_319_, 1);
v_snd_321_ = lean_ctor_get(v_val_320_, 1);
lean_inc(v_snd_321_);
lean_dec(v_val_320_);
v_fst_322_ = lean_ctor_get(v_snd_321_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v_snd_321_, 1);
lean_inc(v_snd_323_);
lean_dec(v_snd_321_);
v___x_324_ = l_Lean_Expr_isFVar(v_fst_322_);
if (v___x_324_ == 0)
{
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
goto v___jp_310_;
}
else
{
uint8_t v___x_325_; 
v___x_325_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_294_, v_fst_322_);
if (v___x_325_ == 0)
{
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
goto v___jp_310_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_295_, v_fst_322_);
if (v___x_326_ == 0)
{
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
goto v___jp_310_;
}
else
{
uint8_t v___x_327_; 
lean_inc_ref(v_y_303_);
v___x_327_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_309_, v_y_303_);
if (v___x_327_ == 0)
{
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
goto v___jp_310_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_294_, v_fst_322_);
if (lean_obj_tag(v___x_328_) == 1)
{
lean_object* v_val_329_; lean_object* v___x_330_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_295_, v_fst_322_);
if (lean_obj_tag(v___x_330_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Array_eraseIdx___redArg(v_ys_294_, v_val_329_);
v___x_333_ = 0;
v___x_334_ = lean_box(v___x_333_);
v___x_335_ = lean_array_set(v_mask_296_, v_val_331_, v___x_334_);
lean_dec(v_val_331_);
v_sz_336_ = lean_array_size(v_args_295_);
v___x_337_ = ((size_t)0ULL);
lean_inc_n(v_snd_323_, 2);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_322_, v_snd_323_, v_sz_336_, v___x_337_, v_args_295_);
v___x_339_ = l_Lean_Meta_mkEqRefl(v_snd_323_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc_n(v_a_340_, 2);
lean_dec_ref_known(v___x_339_, 1);
lean_inc(v_fst_322_);
v___x_341_ = l_Lean_Expr_replaceFVar(v___x_309_, v_fst_322_, v_snd_323_);
lean_dec_ref(v___x_309_);
v___x_342_ = l_Lean_Expr_fvarId_x21(v_fst_322_);
lean_dec(v_fst_322_);
v___x_343_ = l_Lean_Expr_fvarId_x21(v_y_303_);
lean_dec_ref(v_y_303_);
v___x_344_ = lean_array_push(v___x_338_, v_a_340_);
v___x_345_ = lean_box(v___x_333_);
v___x_346_ = lean_array_push(v___x_335_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_i_298_, v___x_347_);
v___x_349_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed), 13, 8);
lean_closure_set(v___x_349_, 0, v_altType_299_);
lean_closure_set(v___x_349_, 1, v_altInfo_300_);
lean_closure_set(v___x_349_, 2, v_k_301_);
lean_closure_set(v___x_349_, 3, v___x_332_);
lean_closure_set(v___x_349_, 4, v___x_344_);
lean_closure_set(v___x_349_, 5, v___x_346_);
lean_closure_set(v___x_349_, 6, v___x_348_);
lean_closure_set(v___x_349_, 7, v___x_341_);
v___x_350_ = lean_alloc_closure((void*)(l_Lean_Meta_withReplaceFVarId___boxed), 9, 4);
lean_closure_set(v___x_350_, 0, lean_box(0));
lean_closure_set(v___x_350_, 1, v___x_343_);
lean_closure_set(v___x_350_, 2, v_a_340_);
lean_closure_set(v___x_350_, 3, v___x_349_);
v___x_351_ = l_Lean_Meta_withReplaceFVarId___redArg(v___x_342_, v_snd_323_, v___x_350_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
return v___x_351_;
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___x_338_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_332_);
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_303_);
lean_dec_ref(v_k_301_);
lean_dec_ref(v_altInfo_300_);
lean_dec_ref(v_altType_299_);
v_a_352_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_339_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_339_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_330_);
lean_dec(v_val_329_);
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
v___x_361_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_360_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_dec_ref_known(v___x_361_, 1);
goto v___jp_310_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_303_);
lean_dec_ref(v_k_301_);
lean_dec_ref(v_altInfo_300_);
lean_dec_ref(v_altType_299_);
lean_dec_ref(v_mask_296_);
lean_dec_ref(v_args_295_);
lean_dec_ref(v_ys_294_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
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
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v___x_328_);
lean_dec(v_snd_323_);
lean_dec(v_fst_322_);
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
v___x_371_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_370_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_dec_ref_known(v___x_371_, 1);
goto v___jp_310_;
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_303_);
lean_dec_ref(v_k_301_);
lean_dec_ref(v_altInfo_300_);
lean_dec_ref(v_altType_299_);
lean_dec_ref(v_mask_296_);
lean_dec_ref(v_args_295_);
lean_dec_ref(v_ys_294_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
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
lean_dec(v_a_319_);
goto v___jp_310_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v_y_303_);
lean_dec_ref(v_k_301_);
lean_dec_ref(v_altInfo_300_);
lean_dec_ref(v_altType_299_);
lean_dec_ref(v_mask_296_);
lean_dec_ref(v_args_295_);
lean_dec_ref(v_ys_294_);
v_a_380_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_318_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_318_);
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
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc_ref(v_y_303_);
v___x_311_ = lean_array_push(v_ys_294_, v_y_303_);
v___x_312_ = lean_array_push(v_args_295_, v_y_303_);
v___x_313_ = lean_box(v___x_297_);
v___x_314_ = lean_array_push(v_mask_296_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_i_298_, v___x_315_);
v___x_317_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_299_, v_altInfo_300_, v_k_301_, v___x_311_, v___x_312_, v___x_314_, v___x_316_, v___x_309_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(lean_object* v_body_388_, lean_object* v_ys_389_, lean_object* v_args_390_, lean_object* v_mask_391_, lean_object* v___x_392_, lean_object* v_i_393_, lean_object* v_altType_394_, lean_object* v_altInfo_395_, lean_object* v_k_396_, lean_object* v_a_397_, lean_object* v_y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_4070__boxed_404_; lean_object* v_res_405_; 
v___x_4070__boxed_404_ = lean_unbox(v___x_392_);
v_res_405_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_body_388_, v_ys_389_, v_args_390_, v_mask_391_, v___x_4070__boxed_404_, v_i_393_, v_altType_394_, v_altInfo_395_, v_k_396_, v_a_397_, v_y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
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
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_whnfForall(v_type_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; uint8_t v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_nat_dec_lt(v_i_728_, v_numDiscrEqs_722_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_i_728_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v___x_738_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_736_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
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
if (lean_obj_tag(v_a_736_) == 7)
{
lean_object* v_binderName_749_; lean_object* v_binderType_750_; lean_object* v_body_751_; lean_object* v_arg_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___x_760_; 
v_binderName_749_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_binderName_749_);
v_binderType_750_ = lean_ctor_get(v_a_736_, 1);
lean_inc_ref_n(v_binderType_750_, 2);
v_body_751_ = lean_ctor_get(v_a_736_, 2);
lean_inc_ref(v_body_751_);
lean_dec_ref_known(v_a_736_, 3);
v___x_760_ = l_Lean_Meta_matchEq_x3f(v_binderType_750_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
if (lean_obj_tag(v_a_761_) == 1)
{
lean_object* v_val_762_; lean_object* v_snd_763_; lean_object* v_snd_764_; lean_object* v___x_765_; 
v_val_762_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_a_761_, 1);
v_snd_763_ = lean_ctor_get(v_val_762_, 1);
lean_inc(v_snd_763_);
lean_dec(v_val_762_);
v_snd_764_ = lean_ctor_get(v_snd_763_, 1);
lean_inc(v_snd_764_);
lean_dec(v_snd_763_);
v___x_765_ = l_Lean_Meta_mkEqRefl(v_snd_764_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_arg_753_ = v_a_766_;
v___y_754_ = v_a_730_;
v___y_755_ = v_a_731_;
v___y_756_ = v_a_732_;
v___y_757_ = v_a_733_;
goto v___jp_752_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_body_751_);
lean_dec_ref(v_binderType_750_);
lean_dec(v_binderName_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_767_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_775_; 
lean_dec(v_a_761_);
lean_inc_ref(v_binderType_750_);
v___x_775_ = l_Lean_Meta_matchHEq_x3f(v_binderType_750_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
if (lean_obj_tag(v_a_776_) == 1)
{
lean_object* v_val_777_; lean_object* v_snd_778_; lean_object* v_snd_779_; lean_object* v_snd_780_; lean_object* v___x_781_; 
v_val_777_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_a_776_, 1);
v_snd_778_ = lean_ctor_get(v_val_777_, 1);
lean_inc(v_snd_778_);
lean_dec(v_val_777_);
v_snd_779_ = lean_ctor_get(v_snd_778_, 1);
lean_inc(v_snd_779_);
lean_dec(v_snd_778_);
v_snd_780_ = lean_ctor_get(v_snd_779_, 1);
lean_inc(v_snd_780_);
lean_dec(v_snd_779_);
v___x_781_ = l_Lean_Meta_mkHEqRefl(v_snd_780_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_arg_753_ = v_a_782_;
v___y_754_ = v_a_730_;
v___y_755_ = v_a_731_;
v___y_756_ = v_a_732_;
v___y_757_ = v_a_733_;
goto v___jp_752_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_body_751_);
lean_dec_ref(v_binderType_750_);
lean_dec(v_binderName_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_783_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_781_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_781_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v_a_776_);
v___x_791_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
lean_inc_ref(v_altType_721_);
v___x_792_ = l_Lean_indentExpr(v_altType_721_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_793_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v_arg_753_ = v_a_795_;
v___y_754_ = v_a_730_;
v___y_755_ = v_a_731_;
v___y_756_ = v_a_732_;
v___y_757_ = v_a_733_;
goto v___jp_752_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_body_751_);
lean_dec_ref(v_binderType_750_);
lean_dec(v_binderName_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_796_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_794_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_body_751_);
lean_dec_ref(v_binderType_750_);
lean_dec(v_binderName_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_804_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_775_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_775_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_body_751_);
lean_dec_ref(v_binderType_750_);
lean_dec(v_binderName_749_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_812_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_760_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_760_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
v___jp_752_:
{
lean_object* v___f_758_; lean_object* v___x_759_; 
v___f_758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_758_, 0, v_body_751_);
lean_closure_set(v___f_758_, 1, v_eqs_725_);
lean_closure_set(v___f_758_, 2, v_args_726_);
lean_closure_set(v___f_758_, 3, v_arg_753_);
lean_closure_set(v___f_758_, 4, v_mask_727_);
lean_closure_set(v___f_758_, 5, v_i_728_);
lean_closure_set(v___f_758_, 6, v_altType_721_);
lean_closure_set(v___f_758_, 7, v_numDiscrEqs_722_);
lean_closure_set(v___f_758_, 8, v_k_723_);
lean_closure_set(v___f_758_, 9, v_ys_724_);
v___x_759_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_749_, v_binderType_750_, v___f_758_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
return v___x_759_;
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_a_736_);
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
v___x_821_ = l_Nat_reprFast(v_numDiscrEqs_722_);
v___x_822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = l_Lean_MessageData_ofFormat(v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_820_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3, &l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_indentExpr(v_altType_721_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_828_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_829_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_i_728_);
lean_dec_ref(v_mask_727_);
lean_dec_ref(v_args_726_);
lean_dec_ref(v_eqs_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_k_723_);
lean_dec(v_numDiscrEqs_722_);
lean_dec_ref(v_altType_721_);
v_a_830_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_735_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_735_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(lean_object* v_body_838_, lean_object* v_eqs_839_, lean_object* v_args_840_, lean_object* v_arg_841_, lean_object* v_mask_842_, lean_object* v_i_843_, lean_object* v_altType_844_, lean_object* v_numDiscrEqs_845_, lean_object* v_k_846_, lean_object* v_ys_847_, lean_object* v_eq_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_854_ = lean_expr_instantiate1(v_body_838_, v_eq_848_);
v___x_855_ = lean_array_push(v_eqs_839_, v_eq_848_);
v___x_856_ = lean_array_push(v_args_840_, v_arg_841_);
v___x_857_ = 0;
v___x_858_ = lean_box(v___x_857_);
v___x_859_ = lean_array_push(v_mask_842_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_i_843_, v___x_860_);
v___x_862_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_844_, v_numDiscrEqs_845_, v_k_846_, v_ys_847_, v___x_855_, v___x_856_, v___x_859_, v___x_861_, v___x_854_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(lean_object* v_altType_863_, lean_object* v_numDiscrEqs_864_, lean_object* v_k_865_, lean_object* v_ys_866_, lean_object* v_eqs_867_, lean_object* v_args_868_, lean_object* v_mask_869_, lean_object* v_i_870_, lean_object* v_type_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_863_, v_numDiscrEqs_864_, v_k_865_, v_ys_866_, v_eqs_867_, v_args_868_, v_mask_869_, v_i_870_, v_type_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(lean_object* v_00_u03b1_878_, lean_object* v_altType_879_, lean_object* v_numDiscrEqs_880_, lean_object* v_k_881_, lean_object* v_ys_882_, lean_object* v_eqs_883_, lean_object* v_args_884_, lean_object* v_mask_885_, lean_object* v_i_886_, lean_object* v_type_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_879_, v_numDiscrEqs_880_, v_k_881_, v_ys_882_, v_eqs_883_, v_args_884_, v_mask_885_, v_i_886_, v_type_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(lean_object* v_00_u03b1_894_, lean_object* v_altType_895_, lean_object* v_numDiscrEqs_896_, lean_object* v_k_897_, lean_object* v_ys_898_, lean_object* v_eqs_899_, lean_object* v_args_900_, lean_object* v_mask_901_, lean_object* v_i_902_, lean_object* v_type_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(v_00_u03b1_894_, v_altType_895_, v_numDiscrEqs_896_, v_k_897_, v_ys_898_, v_eqs_899_, v_args_900_, v_mask_901_, v_i_902_, v_type_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(lean_object* v_altType_910_, lean_object* v_numDiscrEqs_911_, lean_object* v_k_912_, lean_object* v_ys_913_, lean_object* v_args_914_, lean_object* v_mask_915_, lean_object* v_altType_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = ((lean_object*)(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3));
v___x_924_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(v_altType_910_, v_numDiscrEqs_911_, v_k_912_, v_ys_913_, v___x_923_, v_args_914_, v_mask_915_, v___x_922_, v_altType_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(lean_object* v_altType_925_, lean_object* v_numDiscrEqs_926_, lean_object* v_k_927_, lean_object* v_ys_928_, lean_object* v_args_929_, lean_object* v_mask_930_, lean_object* v_altType_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(v_altType_925_, v_numDiscrEqs_926_, v_k_927_, v_ys_928_, v_args_929_, v_mask_930_, v_altType_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object* v_altType_938_, lean_object* v_altInfo_939_, lean_object* v_numDiscrEqs_940_, lean_object* v_k_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; 
lean_inc_ref(v_altType_938_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_947_, 0, v_altType_938_);
lean_closure_set(v___f_947_, 1, v_numDiscrEqs_940_);
lean_closure_set(v___f_947_, 2, v_k_941_);
v___x_948_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_altType_938_, v_altInfo_939_, v___f_947_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(lean_object* v_altType_949_, lean_object* v_altInfo_950_, lean_object* v_numDiscrEqs_951_, lean_object* v_k_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_949_, v_altInfo_950_, v_numDiscrEqs_951_, v_k_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope(lean_object* v_00_u03b1_959_, lean_object* v_altType_960_, lean_object* v_altInfo_961_, lean_object* v_numDiscrEqs_962_, lean_object* v_k_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_altType_960_, v_altInfo_961_, v_numDiscrEqs_962_, v_k_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_forallAltTelescope___boxed(lean_object* v_00_u03b1_970_, lean_object* v_altType_971_, lean_object* v_altInfo_972_, lean_object* v_numDiscrEqs_973_, lean_object* v_k_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Meta_Match_forallAltTelescope(v_00_u03b1_970_, v_altType_971_, v_altInfo_972_, v_numDiscrEqs_973_, v_k_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
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
