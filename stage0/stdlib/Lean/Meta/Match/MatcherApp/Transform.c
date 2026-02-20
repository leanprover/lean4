// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Transform
// Imports: public import Lean.Meta.Match.MatcherApp.Basic public import Lean.Meta.Match.MatchEqsExt public import Lean.Meta.Match.AltTelescopes public import Lean.Meta.AppBuilder import Lean.Meta.Tactic.Split import Lean.Meta.Tactic.Refl
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "unexpected matcher application, insufficient number of parameters in alternative"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "unexpected matcher application, alternative must have "};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_value;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_value;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6;
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "failed to add argument to matcher application, argument type was not refined by `casesOn`"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected type at MatcherApp.addArg"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2_value;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0;
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "failed to add argument to matcher application, type error when constructing the new motive"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_value;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2;
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "unexpected matcher application, motive must be lambda expression with #"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_value;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_value;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "failed to transfer argument through matcher application, alt type must be telescope with #"};
static const lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0_value;
static lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "failed to transfer argument through matcher application, type error when constructing the new motive"};
static const lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0_value;
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "failed to transfer argument through matcher application, motive must be lambda expression with #"};
static const lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2_value;
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0_value;
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object**);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 33, 22, 82, 100, 121, 126, 178)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__4_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7;
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__0_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2;
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Match.MatcherApp.Transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.MatcherApp.transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: ys.size == splitterAltInfo.numFields\n        "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_empty(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: altInfo.numOverlaps = 0\n      "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__8 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__8_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "failed to transform matcher, type error when constructing splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__0_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "failed to transform matcher, type error when constructing new motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "failed to transform matcher, type error when constructing new pre-splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__2_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nfailed with"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__4_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matcher "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " has no MatchInfo found"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2_value;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Cannot close goal after splitting: "};
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0_value;
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0_value;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " of alternative "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2_value;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " still depends on "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4_value;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1;
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_MatcherApp_inferMatchType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___closed__0_value;
static const lean_closure_object l_Lean_Meta_MatcherApp_inferMatchType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___closed__1_value;
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_11, x_12, x_11, x_12, x_13, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_6, x_1, x_13, x_2, x_13, x_2, x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (x_4 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_get_borrowed(x_36, x_6, x_37);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_38);
x_39 = lean_infer_type(x_38, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_41 = l_Lean_Meta_isExprDefEq(x_5, x_40, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
x_17 = x_2;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_35;
}
else
{
x_17 = x_4;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_35;
}
}
else
{
uint8_t x_44; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_dec_ref(x_5);
x_17 = x_4;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = lean_box(0);
goto block_35;
}
block_35:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_mkLambdaFVars(x_3, x_16, x_13, x_2, x_13, x_2, x_14, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(x_17);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_39; lean_object* x_45; uint8_t x_46; 
x_13 = lean_box(x_1);
x_14 = lean_box(x_2);
lean_inc_ref(x_6);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 5);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_3);
x_45 = lean_array_get_size(x_6);
x_46 = lean_nat_dec_eq(x_45, x_5);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4;
x_48 = l_Nat_reprFast(x_5);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_53, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_39 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_55; 
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_dec(x_5);
x_39 = lean_box(0);
goto block_44;
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
x_23 = 0;
x_24 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_21, x_22, x_15, x_23, x_23, x_18, x_19, x_16, x_17);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
block_38:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_33);
x_36 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_37 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_36, x_31, x_34, x_29, x_30);
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_34;
x_20 = x_37;
goto block_28;
}
else
{
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_34;
x_20 = x_33;
goto block_28;
}
}
block_44:
{
lean_object* x_40; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_40 = l_Lean_Meta_instantiateForall(x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
if (lean_obj_tag(x_40) == 0)
{
x_16 = x_10;
x_17 = x_11;
x_18 = x_8;
x_19 = x_9;
x_20 = x_40;
goto block_28;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = l_Lean_Exception_isInterrupt(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_41);
x_29 = x_10;
x_30 = x_11;
x_31 = x_8;
x_32 = lean_box(0);
x_33 = x_40;
x_34 = x_9;
x_35 = x_43;
goto block_38;
}
else
{
lean_dec(x_41);
x_29 = x_10;
x_30 = x_11;
x_31 = x_8;
x_32 = lean_box(0);
x_33 = x_40;
x_34 = x_9;
x_35 = x_42;
goto block_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_6, x_12);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (x_5 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_4);
x_14 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_14, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = l_Lean_Meta_whnfD(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 7)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_fget_borrowed(x_4, x_6);
x_23 = lean_array_get_borrowed(x_21, x_3, x_6);
x_24 = lean_box(x_13);
x_25 = lean_box(x_5);
lean_inc(x_23);
lean_inc_ref(x_1);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_19);
lean_closure_set(x_26, 4, x_23);
x_27 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_23);
lean_inc(x_22);
x_28 = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(x_22, x_23, x_26, x_27, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_expr_instantiate1(x_20, x_30);
lean_dec_ref(x_20);
x_33 = lean_array_fset(x_4, x_6, x_30);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_6, x_34);
lean_dec(x_6);
x_36 = lean_unbox(x_31);
lean_dec(x_31);
x_2 = x_32;
x_4 = x_33;
x_5 = x_36;
x_6 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_41 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
x_42 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_41, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 1;
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_10, x_11, x_10, x_11, x_12, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget_borrowed(x_1, x_8);
x_10 = l_Lean_Expr_isFVar(x_9);
if (x_10 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get_borrowed(x_12, x_2, x_8);
lean_inc(x_9);
x_14 = l_Lean_Expr_replaceFVar(x_4, x_9, x_13);
lean_dec_ref(x_4);
x_3 = x_8;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = lean_array_fget_borrowed(x_1, x_8);
x_10 = l_Lean_Expr_isFVar(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(x_1, x_2, x_8, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get_borrowed(x_12, x_2, x_8);
lean_inc(x_9);
x_14 = l_Lean_Expr_replaceFVar(x_4, x_9, x_13);
lean_dec_ref(x_4);
x_15 = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(x_1, x_2, x_8, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_array_get_size(x_10);
x_124 = lean_array_get_size(x_3);
x_125 = lean_nat_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_126 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_127 = l_Nat_reprFast(x_124);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_MessageData_ofFormat(x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_132, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
x_96 = x_12;
x_97 = x_13;
x_98 = x_14;
x_99 = x_15;
x_100 = lean_box(0);
goto block_122;
}
block_56:
{
lean_object* x_33; 
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_33 = lean_infer_type(x_17, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_MatcherApp_altNumParams(x_1);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_26, x_34, x_35, x_23, x_21, x_36, x_28, x_29, x_30, x_31);
lean_dec_ref(x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0;
x_41 = lean_array_push(x_40, x_2);
x_42 = l_Array_append___redArg(x_41, x_20);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_22);
lean_ctor_set(x_43, 1, x_18);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_19);
lean_ctor_set(x_43, 4, x_25);
lean_ctor_set(x_43, 5, x_24);
lean_ctor_set(x_43, 6, x_39);
lean_ctor_set(x_43, 7, x_42);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0;
x_46 = lean_array_push(x_45, x_2);
x_47 = l_Array_append___redArg(x_46, x_20);
x_48 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_18);
lean_ctor_set(x_48, 2, x_27);
lean_ctor_set(x_48, 3, x_19);
lean_ctor_set(x_48, 4, x_25);
lean_ctor_set(x_48, 5, x_24);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_37, 0);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
block_95:
{
uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; 
x_71 = 0;
x_72 = 1;
x_73 = 1;
x_74 = l_Lean_Meta_mkLambdaFVars(x_10, x_58, x_71, x_72, x_71, x_72, x_73, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc_ref(x_65);
x_76 = lean_array_to_list(x_65);
lean_inc(x_57);
x_77 = l_Lean_mkConst(x_57, x_76);
x_78 = l_Lean_mkAppN(x_77, x_60);
lean_inc(x_75);
x_79 = l_Lean_Expr_app___override(x_78, x_75);
x_80 = l_Lean_mkAppN(x_79, x_64);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_80);
x_81 = l_Lean_Meta_isTypeCorrect(x_80, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_80);
lean_dec(x_75);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_57);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_84 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2;
x_85 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_84, x_66, x_67, x_68, x_69);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
x_17 = x_80;
x_18 = x_57;
x_19 = x_60;
x_20 = x_59;
x_21 = x_71;
x_22 = x_61;
x_23 = x_62;
x_24 = x_64;
x_25 = x_75;
x_26 = x_63;
x_27 = x_65;
x_28 = x_66;
x_29 = x_67;
x_30 = x_68;
x_31 = x_69;
x_32 = lean_box(0);
goto block_56;
}
}
else
{
uint8_t x_89; 
lean_dec_ref(x_80);
lean_dec(x_75);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_57);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
return x_81;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_57);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_74);
if (x_92 == 0)
{
return x_74;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_74, 0);
lean_inc(x_93);
lean_dec(x_74);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
block_122:
{
lean_object* x_101; 
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc_ref(x_2);
x_101 = lean_infer_type(x_2, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_array_get_size(x_3);
lean_inc(x_102);
x_104 = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(x_3, x_10, x_103, x_102);
lean_inc(x_99);
lean_inc_ref(x_98);
x_105 = l_Lean_mkArrow(x_104, x_11, x_98, x_99);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec_ref(x_105);
x_57 = x_5;
x_58 = x_107;
x_59 = x_6;
x_60 = x_7;
x_61 = x_4;
x_62 = x_8;
x_63 = x_102;
x_64 = x_3;
x_65 = x_9;
x_66 = x_96;
x_67 = x_97;
x_68 = x_98;
x_69 = x_99;
x_70 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec_ref(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_108);
x_110 = l_Lean_Meta_getLevel(x_108, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_array_set(x_9, x_109, x_111);
x_57 = x_5;
x_58 = x_108;
x_59 = x_6;
x_60 = x_7;
x_61 = x_4;
x_62 = x_8;
x_63 = x_102;
x_64 = x_3;
x_65 = x_112;
x_66 = x_96;
x_67 = x_97;
x_68 = x_98;
x_69 = x_99;
x_70 = lean_box(0);
goto block_95;
}
else
{
uint8_t x_113; 
lean_dec(x_108);
lean_dec(x_102);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_102);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_116 = !lean_is_exclusive(x_105);
if (x_116 == 0)
{
return x_105;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_101);
if (x_119 == 0)
{
return x_101;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_101, 0);
lean_inc(x_120);
lean_dec(x_101);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_MatcherApp_addArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_8);
lean_closure_set(x_16, 4, x_9);
lean_closure_set(x_16, 5, x_15);
lean_closure_set(x_16, 6, x_11);
lean_closure_set(x_16, 7, x_14);
lean_closure_set(x_16, 8, x_10);
x_17 = 0;
x_18 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_12, x_16, x_17, x_3, x_4, x_5, x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_addArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_addArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_21; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_21 = l_Lean_Exception_isInterrupt(x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_16);
x_17 = x_22;
goto block_20;
}
else
{
lean_dec(x_16);
x_17 = x_21;
goto block_20;
}
block_20:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
return x_8;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_29; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_29 = l_Lean_Exception_isInterrupt(x_23);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_23);
x_25 = x_30;
goto block_28;
}
else
{
lean_dec(x_23);
x_25 = x_29;
goto block_28;
}
block_28:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_addArg_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = lean_infer_type(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_dec_eq(x_21, x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1;
x_24 = l_Nat_reprFast(x_4);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_29, x_7, x_8, x_9, x_10);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_dec(x_4);
x_12 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_getAppNumArgs(x_6);
x_15 = lean_nat_sub(x_14, x_13);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Expr_getRevArg_x21(x_6, x_17);
x_19 = l_Lean_Meta_mkLambdaFVars(x_5, x_18, x_1, x_2, x_1, x_2, x_3, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = 0;
x_17 = 1;
x_18 = lean_array_fget_borrowed(x_1, x_3);
x_19 = lean_box(x_16);
x_20 = lean_box(x_14);
x_21 = lean_box(x_17);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_18);
x_23 = lean_array_fget_borrowed(x_2, x_3);
lean_inc(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_23);
x_25 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_23, x_24, x_22, x_16, x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_29 = lean_array_push(x_4, x_26);
x_3 = x_28;
x_4 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_2);
x_10 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(x_9, x_10, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_MatcherApp_altNumParams(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
x_16 = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(x_13, x_12, x_14, x_15, x_4, x_5, x_6, x_7);
lean_dec(x_12);
lean_dec_ref(x_13);
return x_16;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_refineThrough___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 1)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_15 = lean_array_fget_borrowed(x_1, x_14);
x_16 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_15);
x_17 = l_Lean_Meta_kabstract(x_4, x_15, x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get_borrowed(x_19, x_2, x_14);
x_21 = lean_expr_instantiate1(x_18, x_20);
lean_dec(x_18);
x_3 = x_14;
x_4 = x_21;
goto _start;
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec_ref(x_17);
x_3 = x_14;
x_4 = x_23;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_array_get_size(x_8);
x_88 = lean_array_get_size(x_2);
x_89 = lean_nat_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_90 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
x_91 = l_Nat_reprFast(x_88);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_96, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
else
{
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = lean_box(0);
goto block_86;
}
block_29:
{
lean_object* x_23; 
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
x_23 = lean_infer_type(x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(x_24, x_15, x_16, x_18, x_19, x_20, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
block_64:
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = 0;
x_41 = 1;
x_42 = 1;
x_43 = l_Lean_Meta_mkLambdaFVars(x_8, x_30, x_40, x_41, x_40, x_41, x_42, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_to_list(x_34);
x_46 = l_Lean_mkConst(x_32, x_45);
x_47 = l_Lean_mkAppN(x_46, x_33);
x_48 = l_Lean_Expr_app___override(x_47, x_44);
x_49 = l_Lean_mkAppN(x_48, x_31);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_49);
x_50 = l_Lean_Meta_isTypeCorrect(x_49, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec_ref(x_49);
lean_dec_ref(x_1);
x_53 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
x_54 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_53, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
else
{
x_15 = x_1;
x_16 = x_40;
x_17 = x_49;
x_18 = x_35;
x_19 = x_36;
x_20 = x_37;
x_21 = x_38;
x_22 = lean_box(0);
goto block_29;
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_49);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_50, 0);
lean_inc(x_59);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_32);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_43);
if (x_61 == 0)
{
return x_43;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
block_86:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_array_get_size(x_2);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
x_71 = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_2, x_8, x_70, x_3, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_72);
x_73 = l_Lean_Meta_mkEq(x_72, x_72, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec_ref(x_73);
x_30 = x_75;
x_31 = x_2;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_68;
x_39 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec_ref(x_73);
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_box(0);
x_79 = lean_array_set(x_7, x_77, x_78);
x_30 = x_76;
x_31 = x_2;
x_32 = x_5;
x_33 = x_6;
x_34 = x_79;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_68;
x_39 = lean_box(0);
goto block_64;
}
}
else
{
uint8_t x_80; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_71);
if (x_83 == 0)
{
return x_71;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
lean_dec(x_71);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_MatcherApp_refineThrough___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_8);
lean_closure_set(x_15, 4, x_9);
lean_closure_set(x_15, 5, x_11);
lean_closure_set(x_15, 6, x_10);
x_16 = 0;
x_17 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_12, x_15, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_refineThrough(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_refineThrough(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_21; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_21 = l_Lean_Exception_isInterrupt(x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_16);
x_17 = x_22;
goto block_20;
}
else
{
lean_dec(x_16);
x_17 = x_21;
goto block_20;
}
block_20:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
return x_8;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_29; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_29 = l_Lean_Exception_isInterrupt(x_23);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_23);
x_25 = x_30;
goto block_28;
}
else
{
lean_dec(x_23);
x_25 = x_29;
goto block_28;
}
block_28:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_refineThrough_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
lean_ctor_set(x_3, 2, x_1);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_16);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 1, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 2, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 3, x_20);
x_22 = lean_apply_5(x_2, x_21, x_4, x_5, x_6, lean_box(0));
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_10 = l_Lean_LocalContext_setUserName(x_4, x_9, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 2);
x_10 = l_Array_zip___redArg(x_1, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc_ref(x_9);
lean_dec_ref(x_10);
x_14 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_9, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
if (x_13 == 0)
{
lean_object* x_16; 
lean_inc_ref(x_9);
lean_dec_ref(x_10);
x_16 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_9, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_12);
lean_inc_ref(x_9);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(x_10, x_17, x_18, x_9);
lean_dec_ref(x_10);
x_20 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_12);
lean_inc_ref(x_9);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(x_10, x_21, x_22, x_9);
lean_dec_ref(x_10);
x_24 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(x_23, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
x_11 = lean_apply_1(x_8, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_withUserNames___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_2(x_1, x_3, x_4);
x_13 = lean_apply_7(x_2, lean_box(0), x_12, x_7, x_8, x_9, x_10, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
x_11 = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
x_11 = lean_apply_1(x_8, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_5 = l_Lean_throwError___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_push(x_1, x_7);
x_9 = lean_nat_add(x_2, x_3);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_5, lean_box(0), x_11);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkEqRefl(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkHEqRefl(x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 2);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_6);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_free_object(x_8);
lean_free_object(x_6);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_10, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_13, x_14);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_14, x_24);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_25);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 5, 4);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_12);
lean_closure_set(x_26, 2, x_10);
lean_closure_set(x_26, 3, x_1);
x_27 = lean_box(0);
x_28 = lean_apply_2(x_1, lean_box(0), x_27);
x_29 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_28, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec_ref(x_23);
lean_inc(x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_31, 0, x_12);
lean_closure_set(x_31, 1, x_11);
lean_closure_set(x_31, 2, x_24);
lean_closure_set(x_31, 3, x_10);
lean_closure_set(x_31, 4, x_1);
lean_closure_set(x_31, 5, x_2);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_4);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_33, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_35 = lean_array_fget(x_13, x_14);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_14, x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 5, 4);
lean_closure_set(x_39, 0, x_11);
lean_closure_set(x_39, 1, x_12);
lean_closure_set(x_39, 2, x_38);
lean_closure_set(x_39, 3, x_1);
x_40 = lean_box(0);
x_41 = lean_apply_2(x_1, lean_box(0), x_40);
x_42 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_41, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec_ref(x_35);
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_44, 0, x_12);
lean_closure_set(x_44, 1, x_11);
lean_closure_set(x_44, 2, x_36);
lean_closure_set(x_44, 3, x_38);
lean_closure_set(x_44, 4, x_1);
lean_closure_set(x_44, 5, x_2);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_4);
x_46 = lean_apply_2(x_3, lean_box(0), x_45);
x_47 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_46, x_44);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 2);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_6, 1, x_55);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_6);
x_57 = lean_apply_2(x_1, lean_box(0), x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc(x_53);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_free_object(x_6);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = lean_array_fget(x_51, x_52);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_52, x_60);
lean_dec(x_52);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 5, 4);
lean_closure_set(x_63, 0, x_49);
lean_closure_set(x_63, 1, x_50);
lean_closure_set(x_63, 2, x_62);
lean_closure_set(x_63, 3, x_1);
x_64 = lean_box(0);
x_65 = lean_apply_2(x_1, lean_box(0), x_64);
x_66 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_65, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec_ref(x_59);
lean_inc(x_2);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_68, 0, x_50);
lean_closure_set(x_68, 1, x_49);
lean_closure_set(x_68, 2, x_60);
lean_closure_set(x_68, 3, x_62);
lean_closure_set(x_68, 4, x_1);
lean_closure_set(x_68, 5, x_2);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_4);
x_70 = lean_apply_2(x_3, lean_box(0), x_69);
x_71 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_70, x_68);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_ctor_get(x_6, 1);
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_72);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
x_79 = lean_ctor_get(x_73, 2);
x_80 = lean_nat_dec_lt(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_apply_2(x_1, lean_box(0), x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_79);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_dec(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_85 = x_73;
} else {
 lean_dec_ref(x_73);
 x_85 = lean_box(0);
}
x_86 = lean_array_fget(x_77, x_78);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_78, x_87);
lean_dec(x_78);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_79);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 5, 4);
lean_closure_set(x_90, 0, x_74);
lean_closure_set(x_90, 1, x_75);
lean_closure_set(x_90, 2, x_89);
lean_closure_set(x_90, 3, x_1);
x_91 = lean_box(0);
x_92 = lean_apply_2(x_1, lean_box(0), x_91);
x_93 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_92, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec_ref(x_86);
lean_inc(x_2);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(x_95, 0, x_75);
lean_closure_set(x_95, 1, x_74);
lean_closure_set(x_95, 2, x_87);
lean_closure_set(x_95, 3, x_89);
lean_closure_set(x_95, 4, x_1);
lean_closure_set(x_95, 5, x_2);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_4);
x_97 = lean_apply_2(x_3, lean_box(0), x_96);
x_98 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_97, x_95);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_apply_2(x_6, lean_box(0), x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkArrow(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_apply_2(x_6, lean_box(0), x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Expr_isHEq(x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_array_push(x_2, x_11);
x_13 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0));
x_14 = lean_array_push(x_3, x_13);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 7, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_6, lean_box(0), x_16);
x_18 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed), 8, 7);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
x_12 = lean_apply_2(x_8, lean_box(0), x_10);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13) {
_start:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = lean_apply_2(x_3, lean_box(0), x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_array_push(x_6, x_17);
x_19 = lean_array_push(x_7, x_8);
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_9);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_10);
lean_closure_set(x_20, 4, x_11);
lean_closure_set(x_20, 5, x_12);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_12, lean_box(0), x_21);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg___lam__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_7);
x_28 = lean_apply_2(x_1, lean_box(0), x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_12, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_12, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
x_35 = lean_ctor_get(x_15, 2);
x_36 = lean_array_fget(x_23, x_24);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_24, x_37);
lean_dec(x_24);
lean_ctor_set(x_12, 1, x_38);
x_39 = lean_nat_dec_lt(x_34, x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_7);
x_41 = lean_apply_2(x_1, lean_box(0), x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_8);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_15, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_15, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_15, 0);
lean_dec(x_45);
x_46 = lean_array_fget(x_33, x_34);
x_47 = lean_nat_add(x_34, x_37);
lean_dec(x_34);
lean_ctor_set(x_15, 1, x_47);
if (x_3 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_55;
}
else
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_15);
lean_inc_ref(x_12);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_22);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_56, 0, x_22);
lean_closure_set(x_56, 1, x_18);
lean_closure_set(x_56, 2, x_21);
lean_closure_set(x_56, 3, x_12);
lean_closure_set(x_56, 4, x_15);
lean_closure_set(x_56, 5, x_1);
lean_closure_set(x_56, 6, x_2);
lean_closure_set(x_56, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_57, 0, x_46);
lean_closure_set(x_57, 1, x_5);
lean_closure_set(x_57, 2, x_4);
lean_closure_set(x_57, 3, x_2);
lean_closure_set(x_57, 4, x_56);
lean_closure_set(x_57, 5, x_18);
lean_closure_set(x_57, 6, x_21);
lean_closure_set(x_57, 7, x_36);
lean_closure_set(x_57, 8, x_22);
lean_closure_set(x_57, 9, x_12);
lean_closure_set(x_57, 10, x_15);
lean_closure_set(x_57, 11, x_1);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_58, 0, x_5);
x_59 = lean_apply_2(x_4, lean_box(0), x_58);
x_60 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_59, x_57);
return x_60;
}
else
{
lean_dec(x_46);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_55;
}
}
block_55:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_box(0);
x_49 = lean_array_push(x_18, x_48);
x_50 = lean_array_push(x_21, x_36);
lean_inc(x_1);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_22);
lean_closure_set(x_51, 2, x_49);
lean_closure_set(x_51, 3, x_12);
lean_closure_set(x_51, 4, x_15);
lean_closure_set(x_51, 5, x_1);
x_52 = lean_box(0);
x_53 = lean_apply_2(x_1, lean_box(0), x_52);
x_54 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_53, x_51);
return x_54;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
x_61 = lean_array_fget(x_33, x_34);
x_62 = lean_nat_add(x_34, x_37);
lean_dec(x_34);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_35);
if (x_3 == 0)
{
lean_dec(x_61);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_71;
}
else
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_63);
lean_inc_ref(x_12);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_22);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_72, 0, x_22);
lean_closure_set(x_72, 1, x_18);
lean_closure_set(x_72, 2, x_21);
lean_closure_set(x_72, 3, x_12);
lean_closure_set(x_72, 4, x_63);
lean_closure_set(x_72, 5, x_1);
lean_closure_set(x_72, 6, x_2);
lean_closure_set(x_72, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_73, 0, x_61);
lean_closure_set(x_73, 1, x_5);
lean_closure_set(x_73, 2, x_4);
lean_closure_set(x_73, 3, x_2);
lean_closure_set(x_73, 4, x_72);
lean_closure_set(x_73, 5, x_18);
lean_closure_set(x_73, 6, x_21);
lean_closure_set(x_73, 7, x_36);
lean_closure_set(x_73, 8, x_22);
lean_closure_set(x_73, 9, x_12);
lean_closure_set(x_73, 10, x_63);
lean_closure_set(x_73, 11, x_1);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_74, 0, x_5);
x_75 = lean_apply_2(x_4, lean_box(0), x_74);
x_76 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_75, x_73);
return x_76;
}
else
{
lean_dec(x_61);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_71;
}
}
block_71:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_box(0);
x_65 = lean_array_push(x_18, x_64);
x_66 = lean_array_push(x_21, x_36);
lean_inc(x_1);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_22);
lean_closure_set(x_67, 2, x_65);
lean_closure_set(x_67, 3, x_12);
lean_closure_set(x_67, 4, x_63);
lean_closure_set(x_67, 5, x_1);
x_68 = lean_box(0);
x_69 = lean_apply_2(x_1, lean_box(0), x_68);
x_70 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_69, x_67);
return x_70;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_12);
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
x_79 = lean_ctor_get(x_15, 2);
x_80 = lean_array_fget(x_23, x_24);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_24, x_81);
lean_dec(x_24);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_23);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_25);
x_84 = lean_nat_dec_lt(x_78, x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_7);
x_86 = lean_apply_2(x_1, lean_box(0), x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc(x_79);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_8);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_87 = x_15;
} else {
 lean_dec_ref(x_15);
 x_87 = lean_box(0);
}
x_88 = lean_array_fget(x_77, x_78);
x_89 = lean_nat_add(x_78, x_81);
lean_dec(x_78);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_77);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_79);
if (x_3 == 0)
{
lean_dec(x_88);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_98;
}
else
{
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_90);
lean_inc_ref(x_83);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_22);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_99, 0, x_22);
lean_closure_set(x_99, 1, x_18);
lean_closure_set(x_99, 2, x_21);
lean_closure_set(x_99, 3, x_83);
lean_closure_set(x_99, 4, x_90);
lean_closure_set(x_99, 5, x_1);
lean_closure_set(x_99, 6, x_2);
lean_closure_set(x_99, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_100 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_100, 0, x_88);
lean_closure_set(x_100, 1, x_5);
lean_closure_set(x_100, 2, x_4);
lean_closure_set(x_100, 3, x_2);
lean_closure_set(x_100, 4, x_99);
lean_closure_set(x_100, 5, x_18);
lean_closure_set(x_100, 6, x_21);
lean_closure_set(x_100, 7, x_80);
lean_closure_set(x_100, 8, x_22);
lean_closure_set(x_100, 9, x_83);
lean_closure_set(x_100, 10, x_90);
lean_closure_set(x_100, 11, x_1);
x_101 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_101, 0, x_5);
x_102 = lean_apply_2(x_4, lean_box(0), x_101);
x_103 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_102, x_100);
return x_103;
}
else
{
lean_dec(x_88);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_98;
}
}
block_98:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_box(0);
x_92 = lean_array_push(x_18, x_91);
x_93 = lean_array_push(x_21, x_80);
lean_inc(x_1);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_94, 0, x_93);
lean_closure_set(x_94, 1, x_22);
lean_closure_set(x_94, 2, x_92);
lean_closure_set(x_94, 3, x_83);
lean_closure_set(x_94, 4, x_90);
lean_closure_set(x_94, 5, x_1);
x_95 = lean_box(0);
x_96 = lean_apply_2(x_1, lean_box(0), x_95);
x_97 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_96, x_94);
return x_97;
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_10, 0);
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_10);
x_106 = lean_ctor_get(x_12, 0);
x_107 = lean_ctor_get(x_12, 1);
x_108 = lean_ctor_get(x_12, 2);
x_109 = lean_nat_dec_lt(x_107, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_105);
lean_ctor_set(x_9, 1, x_110);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_7);
x_112 = lean_apply_2(x_1, lean_box(0), x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_inc(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_113 = x_12;
} else {
 lean_dec_ref(x_12);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_15, 0);
x_115 = lean_ctor_get(x_15, 1);
x_116 = lean_ctor_get(x_15, 2);
x_117 = lean_array_fget(x_106, x_107);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_107, x_118);
lean_dec(x_107);
if (lean_is_scalar(x_113)) {
 x_120 = lean_alloc_ctor(0, 3, 0);
} else {
 x_120 = x_113;
}
lean_ctor_set(x_120, 0, x_106);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_108);
x_121 = lean_nat_dec_lt(x_115, x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_117);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_104);
lean_ctor_set(x_122, 1, x_105);
lean_ctor_set(x_9, 1, x_122);
lean_ctor_set(x_8, 0, x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_7);
x_124 = lean_apply_2(x_1, lean_box(0), x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_inc(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_8);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_125 = x_15;
} else {
 lean_dec_ref(x_15);
 x_125 = lean_box(0);
}
x_126 = lean_array_fget(x_114, x_115);
x_127 = lean_nat_add(x_115, x_118);
lean_dec(x_115);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_116);
if (x_3 == 0)
{
lean_dec(x_126);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_136;
}
else
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_128);
lean_inc_ref(x_120);
lean_inc(x_104);
lean_inc(x_18);
lean_inc(x_105);
x_137 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_137, 0, x_105);
lean_closure_set(x_137, 1, x_18);
lean_closure_set(x_137, 2, x_104);
lean_closure_set(x_137, 3, x_120);
lean_closure_set(x_137, 4, x_128);
lean_closure_set(x_137, 5, x_1);
lean_closure_set(x_137, 6, x_2);
lean_closure_set(x_137, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_138, 0, x_126);
lean_closure_set(x_138, 1, x_5);
lean_closure_set(x_138, 2, x_4);
lean_closure_set(x_138, 3, x_2);
lean_closure_set(x_138, 4, x_137);
lean_closure_set(x_138, 5, x_18);
lean_closure_set(x_138, 6, x_104);
lean_closure_set(x_138, 7, x_117);
lean_closure_set(x_138, 8, x_105);
lean_closure_set(x_138, 9, x_120);
lean_closure_set(x_138, 10, x_128);
lean_closure_set(x_138, 11, x_1);
x_139 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_139, 0, x_5);
x_140 = lean_apply_2(x_4, lean_box(0), x_139);
x_141 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_140, x_138);
return x_141;
}
else
{
lean_dec(x_126);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_136;
}
}
block_136:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_box(0);
x_130 = lean_array_push(x_18, x_129);
x_131 = lean_array_push(x_104, x_117);
lean_inc(x_1);
x_132 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_132, 0, x_131);
lean_closure_set(x_132, 1, x_105);
lean_closure_set(x_132, 2, x_130);
lean_closure_set(x_132, 3, x_120);
lean_closure_set(x_132, 4, x_128);
lean_closure_set(x_132, 5, x_1);
x_133 = lean_box(0);
x_134 = lean_apply_2(x_1, lean_box(0), x_133);
x_135 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_134, x_132);
return x_135;
}
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_142 = lean_ctor_get(x_9, 0);
lean_inc(x_142);
lean_dec(x_9);
x_143 = lean_ctor_get(x_10, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_10, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_145 = x_10;
} else {
 lean_dec_ref(x_10);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_12, 0);
x_147 = lean_ctor_get(x_12, 1);
x_148 = lean_ctor_get(x_12, 2);
x_149 = lean_nat_dec_lt(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_144);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_8, 1, x_151);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_7);
x_153 = lean_apply_2(x_1, lean_box(0), x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_inc(x_148);
lean_inc(x_147);
lean_inc_ref(x_146);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_154 = x_12;
} else {
 lean_dec_ref(x_12);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_15, 0);
x_156 = lean_ctor_get(x_15, 1);
x_157 = lean_ctor_get(x_15, 2);
x_158 = lean_array_fget(x_146, x_147);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_147, x_159);
lean_dec(x_147);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_154;
}
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_148);
x_162 = lean_nat_dec_lt(x_156, x_157);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_145)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_145;
}
lean_ctor_set(x_163, 0, x_143);
lean_ctor_set(x_163, 1, x_144);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_8, 1, x_164);
lean_ctor_set(x_8, 0, x_161);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_7);
x_166 = lean_apply_2(x_1, lean_box(0), x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_dec(x_145);
lean_free_object(x_7);
lean_free_object(x_8);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_167 = x_15;
} else {
 lean_dec_ref(x_15);
 x_167 = lean_box(0);
}
x_168 = lean_array_fget(x_155, x_156);
x_169 = lean_nat_add(x_156, x_159);
lean_dec(x_156);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_155);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_157);
if (x_3 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_178;
}
else
{
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_170);
lean_inc_ref(x_161);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_144);
x_179 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_179, 0, x_144);
lean_closure_set(x_179, 1, x_142);
lean_closure_set(x_179, 2, x_143);
lean_closure_set(x_179, 3, x_161);
lean_closure_set(x_179, 4, x_170);
lean_closure_set(x_179, 5, x_1);
lean_closure_set(x_179, 6, x_2);
lean_closure_set(x_179, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_180 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_180, 0, x_168);
lean_closure_set(x_180, 1, x_5);
lean_closure_set(x_180, 2, x_4);
lean_closure_set(x_180, 3, x_2);
lean_closure_set(x_180, 4, x_179);
lean_closure_set(x_180, 5, x_142);
lean_closure_set(x_180, 6, x_143);
lean_closure_set(x_180, 7, x_158);
lean_closure_set(x_180, 8, x_144);
lean_closure_set(x_180, 9, x_161);
lean_closure_set(x_180, 10, x_170);
lean_closure_set(x_180, 11, x_1);
x_181 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_181, 0, x_5);
x_182 = lean_apply_2(x_4, lean_box(0), x_181);
x_183 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_182, x_180);
return x_183;
}
else
{
lean_dec(x_168);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_178;
}
}
block_178:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_box(0);
x_172 = lean_array_push(x_142, x_171);
x_173 = lean_array_push(x_143, x_158);
lean_inc(x_1);
x_174 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_174, 0, x_173);
lean_closure_set(x_174, 1, x_144);
lean_closure_set(x_174, 2, x_172);
lean_closure_set(x_174, 3, x_161);
lean_closure_set(x_174, 4, x_170);
lean_closure_set(x_174, 5, x_1);
x_175 = lean_box(0);
x_176 = lean_apply_2(x_1, lean_box(0), x_175);
x_177 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_176, x_174);
return x_177;
}
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_184 = lean_ctor_get(x_7, 0);
lean_inc(x_184);
lean_dec(x_7);
x_185 = lean_ctor_get(x_9, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_186 = x_9;
} else {
 lean_dec_ref(x_9);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_10, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_10, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_189 = x_10;
} else {
 lean_dec_ref(x_10);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_12, 0);
x_191 = lean_ctor_get(x_12, 1);
x_192 = lean_ctor_get(x_12, 2);
x_193 = lean_nat_dec_lt(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_188);
if (lean_is_scalar(x_186)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_186;
}
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_8, 1, x_195);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_184);
lean_ctor_set(x_196, 1, x_8);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_apply_2(x_1, lean_box(0), x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_inc(x_192);
lean_inc(x_191);
lean_inc_ref(x_190);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_199 = x_12;
} else {
 lean_dec_ref(x_12);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_184, 0);
x_201 = lean_ctor_get(x_184, 1);
x_202 = lean_ctor_get(x_184, 2);
x_203 = lean_array_fget(x_190, x_191);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_add(x_191, x_204);
lean_dec(x_191);
if (lean_is_scalar(x_199)) {
 x_206 = lean_alloc_ctor(0, 3, 0);
} else {
 x_206 = x_199;
}
lean_ctor_set(x_206, 0, x_190);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_192);
x_207 = lean_nat_dec_lt(x_201, x_202);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_203);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_189)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_189;
}
lean_ctor_set(x_208, 0, x_187);
lean_ctor_set(x_208, 1, x_188);
if (lean_is_scalar(x_186)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_186;
}
lean_ctor_set(x_209, 0, x_185);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_8, 1, x_209);
lean_ctor_set(x_8, 0, x_206);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_184);
lean_ctor_set(x_210, 1, x_8);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_apply_2(x_1, lean_box(0), x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_inc(x_202);
lean_inc(x_201);
lean_inc_ref(x_200);
lean_dec(x_189);
lean_dec(x_186);
lean_free_object(x_8);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 x_213 = x_184;
} else {
 lean_dec_ref(x_184);
 x_213 = lean_box(0);
}
x_214 = lean_array_fget(x_200, x_201);
x_215 = lean_nat_add(x_201, x_204);
lean_dec(x_201);
if (lean_is_scalar(x_213)) {
 x_216 = lean_alloc_ctor(0, 3, 0);
} else {
 x_216 = x_213;
}
lean_ctor_set(x_216, 0, x_200);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_216, 2, x_202);
if (x_3 == 0)
{
lean_dec(x_214);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_224;
}
else
{
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_216);
lean_inc_ref(x_206);
lean_inc(x_187);
lean_inc(x_185);
lean_inc(x_188);
x_225 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_225, 0, x_188);
lean_closure_set(x_225, 1, x_185);
lean_closure_set(x_225, 2, x_187);
lean_closure_set(x_225, 3, x_206);
lean_closure_set(x_225, 4, x_216);
lean_closure_set(x_225, 5, x_1);
lean_closure_set(x_225, 6, x_2);
lean_closure_set(x_225, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_226 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_226, 0, x_214);
lean_closure_set(x_226, 1, x_5);
lean_closure_set(x_226, 2, x_4);
lean_closure_set(x_226, 3, x_2);
lean_closure_set(x_226, 4, x_225);
lean_closure_set(x_226, 5, x_185);
lean_closure_set(x_226, 6, x_187);
lean_closure_set(x_226, 7, x_203);
lean_closure_set(x_226, 8, x_188);
lean_closure_set(x_226, 9, x_206);
lean_closure_set(x_226, 10, x_216);
lean_closure_set(x_226, 11, x_1);
x_227 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_227, 0, x_5);
x_228 = lean_apply_2(x_4, lean_box(0), x_227);
x_229 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_228, x_226);
return x_229;
}
else
{
lean_dec(x_214);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_224;
}
}
block_224:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_217 = lean_box(0);
x_218 = lean_array_push(x_185, x_217);
x_219 = lean_array_push(x_187, x_203);
lean_inc(x_1);
x_220 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_220, 0, x_219);
lean_closure_set(x_220, 1, x_188);
lean_closure_set(x_220, 2, x_218);
lean_closure_set(x_220, 3, x_206);
lean_closure_set(x_220, 4, x_216);
lean_closure_set(x_220, 5, x_1);
x_221 = lean_box(0);
x_222 = lean_apply_2(x_1, lean_box(0), x_221);
x_223 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_222, x_220);
return x_223;
}
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_230 = lean_ctor_get(x_8, 0);
lean_inc(x_230);
lean_dec(x_8);
x_231 = lean_ctor_get(x_7, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_232 = x_7;
} else {
 lean_dec_ref(x_7);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_9, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_234 = x_9;
} else {
 lean_dec_ref(x_9);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_10, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_10, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_237 = x_10;
} else {
 lean_dec_ref(x_10);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_230, 0);
x_239 = lean_ctor_get(x_230, 1);
x_240 = lean_ctor_get(x_230, 2);
x_241 = lean_nat_dec_lt(x_239, x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set(x_242, 1, x_236);
if (lean_is_scalar(x_234)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_234;
}
lean_ctor_set(x_243, 0, x_233);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_230);
lean_ctor_set(x_244, 1, x_243);
if (lean_is_scalar(x_232)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_232;
}
lean_ctor_set(x_245, 0, x_231);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = lean_apply_2(x_1, lean_box(0), x_246);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_inc(x_240);
lean_inc(x_239);
lean_inc_ref(x_238);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 x_248 = x_230;
} else {
 lean_dec_ref(x_230);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_231, 0);
x_250 = lean_ctor_get(x_231, 1);
x_251 = lean_ctor_get(x_231, 2);
x_252 = lean_array_fget(x_238, x_239);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_239, x_253);
lean_dec(x_239);
if (lean_is_scalar(x_248)) {
 x_255 = lean_alloc_ctor(0, 3, 0);
} else {
 x_255 = x_248;
}
lean_ctor_set(x_255, 0, x_238);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_240);
x_256 = lean_nat_dec_lt(x_250, x_251);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_252);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_237)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_237;
}
lean_ctor_set(x_257, 0, x_235);
lean_ctor_set(x_257, 1, x_236);
if (lean_is_scalar(x_234)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_234;
}
lean_ctor_set(x_258, 0, x_233);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_255);
lean_ctor_set(x_259, 1, x_258);
if (lean_is_scalar(x_232)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_232;
}
lean_ctor_set(x_260, 0, x_231);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = lean_apply_2(x_1, lean_box(0), x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_inc(x_251);
lean_inc(x_250);
lean_inc_ref(x_249);
lean_dec(x_237);
lean_dec(x_234);
lean_dec(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 x_263 = x_231;
} else {
 lean_dec_ref(x_231);
 x_263 = lean_box(0);
}
x_264 = lean_array_fget(x_249, x_250);
x_265 = lean_nat_add(x_250, x_253);
lean_dec(x_250);
if (lean_is_scalar(x_263)) {
 x_266 = lean_alloc_ctor(0, 3, 0);
} else {
 x_266 = x_263;
}
lean_ctor_set(x_266, 0, x_249);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set(x_266, 2, x_251);
if (x_3 == 0)
{
lean_dec(x_264);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_274;
}
else
{
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_266);
lean_inc_ref(x_255);
lean_inc(x_235);
lean_inc(x_233);
lean_inc(x_236);
x_275 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 9, 8);
lean_closure_set(x_275, 0, x_236);
lean_closure_set(x_275, 1, x_233);
lean_closure_set(x_275, 2, x_235);
lean_closure_set(x_275, 3, x_255);
lean_closure_set(x_275, 4, x_266);
lean_closure_set(x_275, 5, x_1);
lean_closure_set(x_275, 6, x_2);
lean_closure_set(x_275, 7, x_4);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_276 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___boxed), 13, 12);
lean_closure_set(x_276, 0, x_264);
lean_closure_set(x_276, 1, x_5);
lean_closure_set(x_276, 2, x_4);
lean_closure_set(x_276, 3, x_2);
lean_closure_set(x_276, 4, x_275);
lean_closure_set(x_276, 5, x_233);
lean_closure_set(x_276, 6, x_235);
lean_closure_set(x_276, 7, x_252);
lean_closure_set(x_276, 8, x_236);
lean_closure_set(x_276, 9, x_255);
lean_closure_set(x_276, 10, x_266);
lean_closure_set(x_276, 11, x_1);
x_277 = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(x_277, 0, x_5);
x_278 = lean_apply_2(x_4, lean_box(0), x_277);
x_279 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_278, x_276);
return x_279;
}
else
{
lean_dec(x_264);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_274;
}
}
block_274:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = lean_box(0);
x_268 = lean_array_push(x_233, x_267);
x_269 = lean_array_push(x_235, x_252);
lean_inc(x_1);
x_270 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 7, 6);
lean_closure_set(x_270, 0, x_269);
lean_closure_set(x_270, 1, x_236);
lean_closure_set(x_270, 2, x_268);
lean_closure_set(x_270, 3, x_255);
lean_closure_set(x_270, 4, x_266);
lean_closure_set(x_270, 5, x_1);
x_271 = lean_box(0);
x_272 = lean_apply_2(x_1, lean_box(0), x_271);
x_273 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_272, x_270);
return x_273;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__15(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 7, 6);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_2);
lean_closure_set(x_12, 5, x_3);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = lean_box(x_13);
x_17 = lean_box(x_14);
x_18 = lean_box(x_13);
x_19 = lean_box(x_14);
x_20 = lean_box(x_15);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_11);
lean_closure_set(x_21, 2, x_16);
lean_closure_set(x_21, 3, x_17);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_19);
lean_closure_set(x_21, 6, x_20);
x_22 = lean_apply_2(x_2, lean_box(0), x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_12);
return x_23;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
x_12 = lean_array_get_size(x_2);
x_13 = l_Array_toSubarray___redArg(x_2, x_10, x_12);
x_14 = lean_array_get_size(x_9);
x_15 = l_Array_toSubarray___redArg(x_9, x_10, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_3);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_3, x_5, x_20, x_21, x_19);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_11);
lean_inc(x_3);
lean_inc_ref(x_6);
lean_inc_ref(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20), 8, 7);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_13);
lean_inc(x_3);
lean_inc_ref(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21), 6, 5);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_17 = lean_array_get_size(x_9);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22), 2, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_21 = l_Nat_reprFast(x_17);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___redArg(x_6, x_10, x_26);
x_28 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_27, x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22), 2, 1);
lean_closure_set(x_29, 0, x_15);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_1, lean_box(0), x_30);
x_32 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_31, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_MatcherApp_transform___redArg___lam__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Array_append___redArg(x_1, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_5);
lean_ctor_set(x_17, 4, x_6);
lean_ctor_set(x_17, 5, x_7);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 4, x_11);
lean_ctor_set(x_18, 5, x_12);
lean_ctor_set(x_18, 6, x_13);
lean_ctor_set(x_18, 7, x_16);
x_19 = lean_apply_2(x_14, lean_box(0), x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 15, 14);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_9);
lean_closure_set(x_21, 9, x_10);
lean_closure_set(x_21, 10, x_11);
lean_closure_set(x_21, 11, x_12);
lean_closure_set(x_21, 12, x_20);
lean_closure_set(x_21, 13, x_13);
x_22 = lean_apply_1(x_14, x_15);
x_23 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_22, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = lean_apply_4(x_3, x_9, x_7, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Array_append___redArg(x_1, x_2);
x_8 = 1;
x_9 = lean_box(x_3);
x_10 = lean_box(x_4);
x_11 = lean_box(x_3);
x_12 = lean_box(x_4);
x_13 = lean_box(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_14, 0, x_7);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
lean_closure_set(x_14, 6, x_13);
x_15 = lean_apply_2(x_5, lean_box(0), x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_4(x_1, x_2, x_3, x_4, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
x_12 = l_Lean_Meta_MatcherApp_withUserNames___redArg(x_6, x_7, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(x_2);
x_15 = lean_box(x_3);
lean_inc(x_4);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 6, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
lean_inc(x_7);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 7, 6);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_7);
lean_closure_set(x_17, 5, x_16);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 8, 7);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_7);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_9);
lean_closure_set(x_18, 6, x_10);
x_19 = l_Lean_Meta_lambdaTelescope___redArg(x_9, x_10, x_8, x_11, x_2);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__30(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(x_1);
x_15 = lean_box(x_2);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed), 13, 11);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = l_Lean_Meta_forallBoundedTelescope___redArg(x_8, x_9, x_13, x_17, x_16, x_1, x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_2);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_push(x_1, x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_13, x_1);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_apply_2(x_2, lean_box(0), x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_39; 
x_29 = lean_ctor_get(x_20, 1);
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 2);
lean_inc(x_13);
lean_inc(x_2);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 4, 3);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_13);
lean_closure_set(x_34, 2, x_16);
x_39 = lean_nat_dec_lt(x_32, x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_14);
x_41 = lean_apply_2(x_2, lean_box(0), x_40);
x_35 = x_41;
goto block_38;
}
else
{
uint8_t x_42; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_43 = lean_ctor_get(x_21, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_21, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_21, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
x_48 = lean_ctor_get(x_26, 2);
x_49 = lean_array_fget(x_31, x_32);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_32, x_50);
lean_dec(x_32);
lean_ctor_set(x_21, 1, x_51);
x_52 = lean_nat_dec_lt(x_47, x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_14);
x_54 = lean_apply_2(x_2, lean_box(0), x_53);
x_35 = x_54;
goto block_38;
}
else
{
uint8_t x_55; 
lean_inc(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_56 = lean_ctor_get(x_26, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_26, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_26, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_23, 0);
x_60 = lean_ctor_get(x_23, 1);
x_61 = lean_ctor_get(x_23, 2);
x_62 = lean_array_fget(x_46, x_47);
x_63 = lean_nat_add(x_47, x_50);
lean_dec(x_47);
lean_ctor_set(x_26, 1, x_63);
x_64 = lean_nat_dec_lt(x_60, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_14);
x_66 = lean_apply_2(x_2, lean_box(0), x_65);
x_35 = x_66;
goto block_38;
}
else
{
uint8_t x_67; 
lean_inc(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_14);
x_67 = !lean_is_exclusive(x_23);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_68 = lean_ctor_get(x_23, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_23, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_23, 0);
lean_dec(x_70);
x_71 = lean_array_fget_borrowed(x_59, x_60);
x_72 = lean_box(x_5);
x_73 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_71);
lean_inc(x_3);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_73);
lean_closure_set(x_74, 2, x_7);
lean_closure_set(x_74, 3, x_8);
lean_closure_set(x_74, 4, x_13);
lean_closure_set(x_74, 5, x_3);
lean_closure_set(x_74, 6, x_71);
lean_closure_set(x_74, 7, x_9);
lean_closure_set(x_74, 8, x_10);
lean_closure_set(x_74, 9, x_11);
lean_closure_set(x_74, 10, x_12);
x_75 = lean_nat_add(x_60, x_50);
lean_dec(x_60);
lean_ctor_set(x_23, 1, x_75);
lean_inc(x_3);
x_76 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_76, 0, x_29);
lean_closure_set(x_76, 1, x_21);
lean_closure_set(x_76, 2, x_26);
lean_closure_set(x_76, 3, x_23);
lean_closure_set(x_76, 4, x_2);
lean_closure_set(x_76, 5, x_3);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_62);
x_78 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_49, x_77, x_74, x_5, x_5);
lean_inc(x_3);
x_79 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_78, x_76);
x_35 = x_79;
goto block_38;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_23);
x_80 = lean_array_fget_borrowed(x_59, x_60);
x_81 = lean_box(x_5);
x_82 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_80);
lean_inc(x_3);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_83, 0, x_81);
lean_closure_set(x_83, 1, x_82);
lean_closure_set(x_83, 2, x_7);
lean_closure_set(x_83, 3, x_8);
lean_closure_set(x_83, 4, x_13);
lean_closure_set(x_83, 5, x_3);
lean_closure_set(x_83, 6, x_80);
lean_closure_set(x_83, 7, x_9);
lean_closure_set(x_83, 8, x_10);
lean_closure_set(x_83, 9, x_11);
lean_closure_set(x_83, 10, x_12);
x_84 = lean_nat_add(x_60, x_50);
lean_dec(x_60);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_59);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_61);
lean_inc(x_3);
x_86 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_86, 0, x_29);
lean_closure_set(x_86, 1, x_21);
lean_closure_set(x_86, 2, x_26);
lean_closure_set(x_86, 3, x_85);
lean_closure_set(x_86, 4, x_2);
lean_closure_set(x_86, 5, x_3);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_62);
x_88 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_49, x_87, x_83, x_5, x_5);
lean_inc(x_3);
x_89 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_88, x_86);
x_35 = x_89;
goto block_38;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_26);
x_90 = lean_ctor_get(x_23, 0);
x_91 = lean_ctor_get(x_23, 1);
x_92 = lean_ctor_get(x_23, 2);
x_93 = lean_array_fget(x_46, x_47);
x_94 = lean_nat_add(x_47, x_50);
lean_dec(x_47);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_46);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_48);
x_96 = lean_nat_dec_lt(x_91, x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_19, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_14);
x_98 = lean_apply_2(x_2, lean_box(0), x_97);
x_35 = x_98;
goto block_38;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_inc(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_14);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_99 = x_23;
} else {
 lean_dec_ref(x_23);
 x_99 = lean_box(0);
}
x_100 = lean_array_fget_borrowed(x_90, x_91);
x_101 = lean_box(x_5);
x_102 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_100);
lean_inc(x_3);
x_103 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_103, 0, x_101);
lean_closure_set(x_103, 1, x_102);
lean_closure_set(x_103, 2, x_7);
lean_closure_set(x_103, 3, x_8);
lean_closure_set(x_103, 4, x_13);
lean_closure_set(x_103, 5, x_3);
lean_closure_set(x_103, 6, x_100);
lean_closure_set(x_103, 7, x_9);
lean_closure_set(x_103, 8, x_10);
lean_closure_set(x_103, 9, x_11);
lean_closure_set(x_103, 10, x_12);
x_104 = lean_nat_add(x_91, x_50);
lean_dec(x_91);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(0, 3, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_90);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_92);
lean_inc(x_3);
x_106 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_106, 0, x_29);
lean_closure_set(x_106, 1, x_21);
lean_closure_set(x_106, 2, x_95);
lean_closure_set(x_106, 3, x_105);
lean_closure_set(x_106, 4, x_2);
lean_closure_set(x_106, 5, x_3);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_93);
x_108 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_49, x_107, x_103, x_5, x_5);
lean_inc(x_3);
x_109 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_108, x_106);
x_35 = x_109;
goto block_38;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_21);
x_110 = lean_ctor_get(x_26, 0);
x_111 = lean_ctor_get(x_26, 1);
x_112 = lean_ctor_get(x_26, 2);
x_113 = lean_array_fget(x_31, x_32);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_32, x_114);
lean_dec(x_32);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_31);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_33);
x_117 = lean_nat_dec_lt(x_111, x_112);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_113);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_20, 0, x_116);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_14);
x_119 = lean_apply_2(x_2, lean_box(0), x_118);
x_35 = x_119;
goto block_38;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_inc(x_112);
lean_inc(x_111);
lean_inc_ref(x_110);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_120 = x_26;
} else {
 lean_dec_ref(x_26);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_23, 0);
x_122 = lean_ctor_get(x_23, 1);
x_123 = lean_ctor_get(x_23, 2);
x_124 = lean_array_fget(x_110, x_111);
x_125 = lean_nat_add(x_111, x_114);
lean_dec(x_111);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_120;
}
lean_ctor_set(x_126, 0, x_110);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_112);
x_127 = lean_nat_dec_lt(x_122, x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_20, 0, x_116);
lean_ctor_set(x_19, 0, x_126);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_14);
x_129 = lean_apply_2(x_2, lean_box(0), x_128);
x_35 = x_129;
goto block_38;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_inc(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_14);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_130 = x_23;
} else {
 lean_dec_ref(x_23);
 x_130 = lean_box(0);
}
x_131 = lean_array_fget_borrowed(x_121, x_122);
x_132 = lean_box(x_5);
x_133 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_131);
lean_inc(x_3);
x_134 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_134, 0, x_132);
lean_closure_set(x_134, 1, x_133);
lean_closure_set(x_134, 2, x_7);
lean_closure_set(x_134, 3, x_8);
lean_closure_set(x_134, 4, x_13);
lean_closure_set(x_134, 5, x_3);
lean_closure_set(x_134, 6, x_131);
lean_closure_set(x_134, 7, x_9);
lean_closure_set(x_134, 8, x_10);
lean_closure_set(x_134, 9, x_11);
lean_closure_set(x_134, 10, x_12);
x_135 = lean_nat_add(x_122, x_114);
lean_dec(x_122);
if (lean_is_scalar(x_130)) {
 x_136 = lean_alloc_ctor(0, 3, 0);
} else {
 x_136 = x_130;
}
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_123);
lean_inc(x_3);
x_137 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_137, 0, x_29);
lean_closure_set(x_137, 1, x_116);
lean_closure_set(x_137, 2, x_126);
lean_closure_set(x_137, 3, x_136);
lean_closure_set(x_137, 4, x_2);
lean_closure_set(x_137, 5, x_3);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_124);
x_139 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_113, x_138, x_134, x_5, x_5);
lean_inc(x_3);
x_140 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_139, x_137);
x_35 = x_140;
goto block_38;
}
}
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
lean_inc(x_3);
x_36 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_35, x_4);
x_37 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_36, x_34);
return x_37;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_150; 
x_141 = lean_ctor_get(x_20, 1);
lean_inc(x_141);
lean_dec(x_20);
x_142 = lean_ctor_get(x_21, 0);
x_143 = lean_ctor_get(x_21, 1);
x_144 = lean_ctor_get(x_21, 2);
lean_inc(x_13);
lean_inc(x_2);
x_145 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 4, 3);
lean_closure_set(x_145, 0, x_2);
lean_closure_set(x_145, 1, x_13);
lean_closure_set(x_145, 2, x_16);
x_150 = lean_nat_dec_lt(x_143, x_144);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_21);
lean_ctor_set(x_151, 1, x_141);
lean_ctor_set(x_19, 1, x_151);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_14);
x_153 = lean_apply_2(x_2, lean_box(0), x_152);
x_146 = x_153;
goto block_149;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_inc(x_144);
lean_inc(x_143);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_154 = x_21;
} else {
 lean_dec_ref(x_21);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_26, 0);
x_156 = lean_ctor_get(x_26, 1);
x_157 = lean_ctor_get(x_26, 2);
x_158 = lean_array_fget(x_142, x_143);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_143, x_159);
lean_dec(x_143);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_154;
}
lean_ctor_set(x_161, 0, x_142);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_144);
x_162 = lean_nat_dec_lt(x_156, x_157);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_141);
lean_ctor_set(x_19, 1, x_163);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_14);
x_165 = lean_apply_2(x_2, lean_box(0), x_164);
x_146 = x_165;
goto block_149;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_166 = x_26;
} else {
 lean_dec_ref(x_26);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_23, 0);
x_168 = lean_ctor_get(x_23, 1);
x_169 = lean_ctor_get(x_23, 2);
x_170 = lean_array_fget(x_155, x_156);
x_171 = lean_nat_add(x_156, x_159);
lean_dec(x_156);
if (lean_is_scalar(x_166)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_166;
}
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_157);
x_173 = lean_nat_dec_lt(x_168, x_169);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_170);
lean_dec(x_158);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_161);
lean_ctor_set(x_174, 1, x_141);
lean_ctor_set(x_19, 1, x_174);
lean_ctor_set(x_19, 0, x_172);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_14);
x_176 = lean_apply_2(x_2, lean_box(0), x_175);
x_146 = x_176;
goto block_149;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_inc(x_169);
lean_inc(x_168);
lean_inc_ref(x_167);
lean_free_object(x_19);
lean_free_object(x_14);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_177 = x_23;
} else {
 lean_dec_ref(x_23);
 x_177 = lean_box(0);
}
x_178 = lean_array_fget_borrowed(x_167, x_168);
x_179 = lean_box(x_5);
x_180 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_178);
lean_inc(x_3);
x_181 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_181, 0, x_179);
lean_closure_set(x_181, 1, x_180);
lean_closure_set(x_181, 2, x_7);
lean_closure_set(x_181, 3, x_8);
lean_closure_set(x_181, 4, x_13);
lean_closure_set(x_181, 5, x_3);
lean_closure_set(x_181, 6, x_178);
lean_closure_set(x_181, 7, x_9);
lean_closure_set(x_181, 8, x_10);
lean_closure_set(x_181, 9, x_11);
lean_closure_set(x_181, 10, x_12);
x_182 = lean_nat_add(x_168, x_159);
lean_dec(x_168);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 3, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_167);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_169);
lean_inc(x_3);
x_184 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_184, 0, x_141);
lean_closure_set(x_184, 1, x_161);
lean_closure_set(x_184, 2, x_172);
lean_closure_set(x_184, 3, x_183);
lean_closure_set(x_184, 4, x_2);
lean_closure_set(x_184, 5, x_3);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_170);
x_186 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_158, x_185, x_181, x_5, x_5);
lean_inc(x_3);
x_187 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_186, x_184);
x_146 = x_187;
goto block_149;
}
}
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
lean_inc(x_3);
x_147 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_146, x_4);
x_148 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_147, x_145);
return x_148;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_199; 
x_188 = lean_ctor_get(x_19, 0);
lean_inc(x_188);
lean_dec(x_19);
x_189 = lean_ctor_get(x_20, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_190 = x_20;
} else {
 lean_dec_ref(x_20);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_21, 0);
x_192 = lean_ctor_get(x_21, 1);
x_193 = lean_ctor_get(x_21, 2);
lean_inc(x_13);
lean_inc(x_2);
x_194 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 4, 3);
lean_closure_set(x_194, 0, x_2);
lean_closure_set(x_194, 1, x_13);
lean_closure_set(x_194, 2, x_16);
x_199 = lean_nat_dec_lt(x_192, x_193);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_190)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_190;
}
lean_ctor_set(x_200, 0, x_21);
lean_ctor_set(x_200, 1, x_189);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_188);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_14, 1, x_201);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_14);
x_203 = lean_apply_2(x_2, lean_box(0), x_202);
x_195 = x_203;
goto block_198;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_inc(x_193);
lean_inc(x_192);
lean_inc_ref(x_191);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_204 = x_21;
} else {
 lean_dec_ref(x_21);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_188, 0);
x_206 = lean_ctor_get(x_188, 1);
x_207 = lean_ctor_get(x_188, 2);
x_208 = lean_array_fget(x_191, x_192);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_192, x_209);
lean_dec(x_192);
if (lean_is_scalar(x_204)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_204;
}
lean_ctor_set(x_211, 0, x_191);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_193);
x_212 = lean_nat_dec_lt(x_206, x_207);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_208);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_190)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_190;
}
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_189);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_188);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_14, 1, x_214);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_14);
x_216 = lean_apply_2(x_2, lean_box(0), x_215);
x_195 = x_216;
goto block_198;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_inc(x_207);
lean_inc(x_206);
lean_inc_ref(x_205);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 x_217 = x_188;
} else {
 lean_dec_ref(x_188);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_23, 0);
x_219 = lean_ctor_get(x_23, 1);
x_220 = lean_ctor_get(x_23, 2);
x_221 = lean_array_fget(x_205, x_206);
x_222 = lean_nat_add(x_206, x_209);
lean_dec(x_206);
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 3, 0);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_205);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_207);
x_224 = lean_nat_dec_lt(x_219, x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_221);
lean_dec(x_208);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_190)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_190;
}
lean_ctor_set(x_225, 0, x_211);
lean_ctor_set(x_225, 1, x_189);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_14, 1, x_226);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_14);
x_228 = lean_apply_2(x_2, lean_box(0), x_227);
x_195 = x_228;
goto block_198;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_inc(x_220);
lean_inc(x_219);
lean_inc_ref(x_218);
lean_dec(x_190);
lean_free_object(x_14);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_229 = x_23;
} else {
 lean_dec_ref(x_23);
 x_229 = lean_box(0);
}
x_230 = lean_array_fget_borrowed(x_218, x_219);
x_231 = lean_box(x_5);
x_232 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_230);
lean_inc(x_3);
x_233 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_233, 0, x_231);
lean_closure_set(x_233, 1, x_232);
lean_closure_set(x_233, 2, x_7);
lean_closure_set(x_233, 3, x_8);
lean_closure_set(x_233, 4, x_13);
lean_closure_set(x_233, 5, x_3);
lean_closure_set(x_233, 6, x_230);
lean_closure_set(x_233, 7, x_9);
lean_closure_set(x_233, 8, x_10);
lean_closure_set(x_233, 9, x_11);
lean_closure_set(x_233, 10, x_12);
x_234 = lean_nat_add(x_219, x_209);
lean_dec(x_219);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(0, 3, 0);
} else {
 x_235 = x_229;
}
lean_ctor_set(x_235, 0, x_218);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_235, 2, x_220);
lean_inc(x_3);
x_236 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_236, 0, x_189);
lean_closure_set(x_236, 1, x_211);
lean_closure_set(x_236, 2, x_223);
lean_closure_set(x_236, 3, x_235);
lean_closure_set(x_236, 4, x_2);
lean_closure_set(x_236, 5, x_3);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_221);
x_238 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_208, x_237, x_233, x_5, x_5);
lean_inc(x_3);
x_239 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_238, x_236);
x_195 = x_239;
goto block_198;
}
}
}
block_198:
{
lean_object* x_196; lean_object* x_197; 
lean_inc(x_3);
x_196 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_195, x_4);
x_197 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_196, x_194);
return x_197;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_253; 
x_240 = lean_ctor_get(x_14, 0);
lean_inc(x_240);
lean_dec(x_14);
x_241 = lean_ctor_get(x_19, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_242 = x_19;
} else {
 lean_dec_ref(x_19);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_20, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_244 = x_20;
} else {
 lean_dec_ref(x_20);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_21, 0);
x_246 = lean_ctor_get(x_21, 1);
x_247 = lean_ctor_get(x_21, 2);
lean_inc(x_13);
lean_inc(x_2);
x_248 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 4, 3);
lean_closure_set(x_248, 0, x_2);
lean_closure_set(x_248, 1, x_13);
lean_closure_set(x_248, 2, x_16);
x_253 = lean_nat_dec_lt(x_246, x_247);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_244)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_244;
}
lean_ctor_set(x_254, 0, x_21);
lean_ctor_set(x_254, 1, x_243);
if (lean_is_scalar(x_242)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_242;
}
lean_ctor_set(x_255, 0, x_241);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_240);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = lean_apply_2(x_2, lean_box(0), x_257);
x_249 = x_258;
goto block_252;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_inc(x_247);
lean_inc(x_246);
lean_inc_ref(x_245);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_259 = x_21;
} else {
 lean_dec_ref(x_21);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_241, 0);
x_261 = lean_ctor_get(x_241, 1);
x_262 = lean_ctor_get(x_241, 2);
x_263 = lean_array_fget(x_245, x_246);
x_264 = lean_unsigned_to_nat(1u);
x_265 = lean_nat_add(x_246, x_264);
lean_dec(x_246);
if (lean_is_scalar(x_259)) {
 x_266 = lean_alloc_ctor(0, 3, 0);
} else {
 x_266 = x_259;
}
lean_ctor_set(x_266, 0, x_245);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set(x_266, 2, x_247);
x_267 = lean_nat_dec_lt(x_261, x_262);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_263);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_244)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_244;
}
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_243);
if (lean_is_scalar(x_242)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_242;
}
lean_ctor_set(x_269, 0, x_241);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_240);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = lean_apply_2(x_2, lean_box(0), x_271);
x_249 = x_272;
goto block_252;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_inc(x_262);
lean_inc(x_261);
lean_inc_ref(x_260);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 x_273 = x_241;
} else {
 lean_dec_ref(x_241);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_240, 0);
x_275 = lean_ctor_get(x_240, 1);
x_276 = lean_ctor_get(x_240, 2);
x_277 = lean_array_fget(x_260, x_261);
x_278 = lean_nat_add(x_261, x_264);
lean_dec(x_261);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 3, 0);
} else {
 x_279 = x_273;
}
lean_ctor_set(x_279, 0, x_260);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set(x_279, 2, x_262);
x_280 = lean_nat_dec_lt(x_275, x_276);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_277);
lean_dec(x_263);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_244)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_244;
}
lean_ctor_set(x_281, 0, x_266);
lean_ctor_set(x_281, 1, x_243);
if (lean_is_scalar(x_242)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_242;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_240);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_285 = lean_apply_2(x_2, lean_box(0), x_284);
x_249 = x_285;
goto block_252;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_inc(x_276);
lean_inc(x_275);
lean_inc_ref(x_274);
lean_dec(x_244);
lean_dec(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_286 = x_240;
} else {
 lean_dec_ref(x_240);
 x_286 = lean_box(0);
}
x_287 = lean_array_fget_borrowed(x_274, x_275);
x_288 = lean_box(x_5);
x_289 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_287);
lean_inc(x_3);
x_290 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_290, 0, x_288);
lean_closure_set(x_290, 1, x_289);
lean_closure_set(x_290, 2, x_7);
lean_closure_set(x_290, 3, x_8);
lean_closure_set(x_290, 4, x_13);
lean_closure_set(x_290, 5, x_3);
lean_closure_set(x_290, 6, x_287);
lean_closure_set(x_290, 7, x_9);
lean_closure_set(x_290, 8, x_10);
lean_closure_set(x_290, 9, x_11);
lean_closure_set(x_290, 10, x_12);
x_291 = lean_nat_add(x_275, x_264);
lean_dec(x_275);
if (lean_is_scalar(x_286)) {
 x_292 = lean_alloc_ctor(0, 3, 0);
} else {
 x_292 = x_286;
}
lean_ctor_set(x_292, 0, x_274);
lean_ctor_set(x_292, 1, x_291);
lean_ctor_set(x_292, 2, x_276);
lean_inc(x_3);
x_293 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 7, 6);
lean_closure_set(x_293, 0, x_243);
lean_closure_set(x_293, 1, x_266);
lean_closure_set(x_293, 2, x_279);
lean_closure_set(x_293, 3, x_292);
lean_closure_set(x_293, 4, x_2);
lean_closure_set(x_293, 5, x_3);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_277);
x_295 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_263, x_294, x_290, x_5, x_5);
lean_inc(x_3);
x_296 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_295, x_293);
x_249 = x_296;
goto block_252;
}
}
}
block_252:
{
lean_object* x_250; lean_object* x_251; 
lean_inc(x_3);
x_250 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_249, x_4);
x_251 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_250, x_248);
return x_251;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_Meta_MatcherApp_altNumParams(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_array_get_size(x_9);
lean_inc(x_3);
x_13 = l_Array_toSubarray___redArg(x_2, x_3, x_4);
lean_inc(x_3);
x_14 = l_Array_toSubarray___redArg(x_10, x_3, x_11);
lean_inc(x_3);
x_15 = l_Array_toSubarray___redArg(x_9, x_3, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_WellFounded_opaqueFix_u2083___redArg(x_6, x_3, x_18, lean_box(0));
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_8);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_array_get_size(x_1);
x_20 = lean_box(x_5);
x_21 = lean_box(x_6);
lean_inc(x_7);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 16, 12);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_8);
lean_closure_set(x_22, 8, x_9);
lean_closure_set(x_22, 9, x_10);
lean_closure_set(x_22, 10, x_11);
lean_closure_set(x_22, 11, x_12);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35), 9, 8);
lean_closure_set(x_23, 0, x_13);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_14);
lean_closure_set(x_23, 3, x_19);
lean_closure_set(x_23, 4, x_15);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_3);
lean_closure_set(x_23, 7, x_16);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_17);
x_25 = lean_apply_2(x_7, lean_box(0), x_24);
x_26 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_23);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_indentD(x_2);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_mapErrorImp___redArg(x_9, x_2, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = lean_apply_4(x_3, x_9, x_7, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_7 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2));
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7;
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Array_append___redArg(x_1, x_2);
x_10 = l_Array_append___redArg(x_9, x_3);
x_11 = l_Array_append___redArg(x_10, x_4);
x_12 = 1;
x_13 = lean_box(x_5);
x_14 = lean_box(x_6);
x_15 = lean_box(x_5);
x_16 = lean_box(x_6);
x_17 = lean_box(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_14);
lean_closure_set(x_18, 4, x_15);
lean_closure_set(x_18, 5, x_16);
lean_closure_set(x_18, 6, x_17);
x_19 = lean_apply_2(x_7, lean_box(0), x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_4(x_1, x_2, x_3, x_4, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_box(x_5);
x_19 = lean_box(x_6);
lean_inc(x_7);
lean_inc_ref(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_7);
x_21 = l_Array_append___redArg(x_8, x_4);
lean_dec_ref(x_4);
lean_inc(x_11);
lean_inc_ref(x_21);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 7, 6);
lean_closure_set(x_22, 0, x_9);
lean_closure_set(x_22, 1, x_10);
lean_closure_set(x_22, 2, x_15);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_11);
lean_closure_set(x_22, 5, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_21);
x_24 = lean_apply_2(x_7, lean_box(0), x_23);
x_25 = lean_apply_3(x_17, lean_box(0), x_24, x_13);
x_26 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_25, x_22);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_4);
x_19 = lean_box(x_5);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 15, 13);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_16);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_9);
lean_closure_set(x_20, 10, x_10);
lean_closure_set(x_20, 11, x_11);
lean_closure_set(x_20, 12, x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_14, x_15, x_17, x_21, x_20, x_4, x_4);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_3);
x_19 = lean_box(x_4);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_16);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_19);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_9);
lean_closure_set(x_20, 10, x_10);
lean_closure_set(x_20, 11, x_11);
lean_closure_set(x_20, 12, x_12);
lean_closure_set(x_20, 13, x_13);
lean_closure_set(x_20, 14, x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_13, x_14, x_17, x_21, x_20, x_3, x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_4);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__45(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_forallBoundedTelescope___redArg(x_2, x_3, x_8, x_10, x_4, x_5, x_5);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2;
x_12 = lean_mk_empty_array_with_capacity(x_5);
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_6, lean_box(0), x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__2));
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(319u);
x_4 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_array_get_size(x_20);
x_24 = lean_nat_dec_eq(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_25 = l_Lean_instInhabitedExpr;
x_26 = l_instInhabitedOfMonad___redArg(x_2, x_25);
x_27 = l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3;
x_28 = l_panic___redArg(x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_box(x_4);
x_30 = lean_box(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_13);
lean_inc(x_9);
lean_inc(x_6);
lean_inc_ref(x_20);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed), 17, 15);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_20);
lean_closure_set(x_31, 2, x_29);
lean_closure_set(x_31, 3, x_30);
lean_closure_set(x_31, 4, x_6);
lean_closure_set(x_31, 5, x_21);
lean_closure_set(x_31, 6, x_7);
lean_closure_set(x_31, 7, x_8);
lean_closure_set(x_31, 8, x_9);
lean_closure_set(x_31, 9, x_10);
lean_closure_set(x_31, 10, x_11);
lean_closure_set(x_31, 11, x_12);
lean_closure_set(x_31, 12, x_13);
lean_closure_set(x_31, 13, x_2);
lean_closure_set(x_31, 14, x_14);
x_32 = lean_box(x_4);
lean_inc(x_9);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 8, 7);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_13);
lean_closure_set(x_33, 2, x_2);
lean_closure_set(x_33, 3, x_31);
lean_closure_set(x_33, 4, x_32);
lean_closure_set(x_33, 5, x_9);
lean_closure_set(x_33, 6, x_15);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_box(x_16);
lean_inc(x_6);
lean_inc_ref(x_34);
lean_inc(x_9);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 8, 7);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_17);
lean_closure_set(x_36, 2, x_9);
lean_closure_set(x_36, 3, x_34);
lean_closure_set(x_36, 4, x_18);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_34);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(x_37, 0, x_19);
lean_closure_set(x_37, 1, x_20);
x_38 = lean_apply_2(x_6, lean_box(0), x_37);
x_39 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_38, x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_4);
x_23 = lean_unbox(x_5);
x_24 = lean_unbox(x_16);
x_25 = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(x_1, x_2, x_3, x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24, x_17, x_18, x_19, x_20, x_21);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_apply_2(x_7, lean_box(0), x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_push(x_1, x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_7, lean_box(0), x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Subarray_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__8));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(317u);
x_4 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_16, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_apply_2(x_2, lean_box(0), x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_50; 
x_40 = lean_ctor_get(x_25, 1);
x_41 = lean_ctor_get(x_25, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
x_44 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_45, 0, x_2);
lean_closure_set(x_45, 1, x_16);
lean_closure_set(x_45, 2, x_19);
x_50 = lean_nat_dec_lt(x_43, x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_17);
x_52 = lean_apply_2(x_2, lean_box(0), x_51);
x_46 = x_52;
goto block_49;
}
else
{
uint8_t x_53; 
lean_inc(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_26, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_26, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_26, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
x_59 = lean_ctor_get(x_37, 2);
x_60 = lean_array_fget(x_42, x_43);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_43, x_61);
lean_dec(x_43);
lean_ctor_set(x_26, 1, x_62);
x_63 = lean_nat_dec_lt(x_58, x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_17);
x_65 = lean_apply_2(x_2, lean_box(0), x_64);
x_46 = x_65;
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
x_66 = !lean_is_exclusive(x_37);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_34, 0);
x_71 = lean_ctor_get(x_34, 1);
x_72 = lean_ctor_get(x_34, 2);
x_73 = lean_array_fget(x_57, x_58);
x_74 = lean_nat_add(x_58, x_61);
lean_dec(x_58);
lean_ctor_set(x_37, 1, x_74);
x_75 = lean_nat_dec_lt(x_71, x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_17);
x_77 = lean_apply_2(x_2, lean_box(0), x_76);
x_46 = x_77;
goto block_49;
}
else
{
uint8_t x_78; 
lean_inc(x_72);
lean_inc(x_71);
lean_inc_ref(x_70);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_34, 2);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_34, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_31, 0);
x_83 = lean_ctor_get(x_31, 1);
x_84 = lean_ctor_get(x_31, 2);
x_85 = lean_array_fget(x_70, x_71);
x_86 = lean_nat_add(x_71, x_61);
lean_dec(x_71);
lean_ctor_set(x_34, 1, x_86);
x_87 = lean_nat_dec_lt(x_83, x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_17);
x_89 = lean_apply_2(x_2, lean_box(0), x_88);
x_46 = x_89;
goto block_49;
}
else
{
uint8_t x_90; 
lean_inc(x_84);
lean_inc(x_83);
lean_inc_ref(x_82);
x_90 = !lean_is_exclusive(x_31);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_91 = lean_ctor_get(x_31, 2);
lean_dec(x_91);
x_92 = lean_ctor_get(x_31, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_31, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_28, 0);
x_95 = lean_ctor_get(x_28, 1);
x_96 = lean_ctor_get(x_28, 2);
x_97 = lean_array_fget(x_82, x_83);
x_98 = lean_nat_add(x_83, x_61);
lean_dec(x_83);
lean_ctor_set(x_31, 1, x_98);
x_99 = lean_nat_dec_lt(x_95, x_96);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_85);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_17);
x_101 = lean_apply_2(x_2, lean_box(0), x_100);
x_46 = x_101;
goto block_49;
}
else
{
uint8_t x_102; 
lean_inc(x_96);
lean_inc(x_95);
lean_inc_ref(x_94);
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
x_102 = !lean_is_exclusive(x_28);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_28, 2);
lean_dec(x_103);
x_104 = lean_ctor_get(x_28, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_28, 0);
lean_dec(x_105);
x_106 = lean_ctor_get(x_97, 1);
x_107 = lean_ctor_get_uint8(x_97, sizeof(void*)*2);
x_108 = lean_nat_dec_eq(x_106, x_5);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_free_object(x_28);
lean_dec_ref(x_31);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_34);
lean_dec(x_85);
lean_dec_ref(x_37);
lean_dec(x_73);
lean_dec_ref(x_26);
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_109 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_110 = l_instInhabitedOfMonad___redArg(x_6, x_109);
x_111 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_112 = l_panic___redArg(x_110, x_111);
x_46 = x_112;
goto block_49;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_85);
x_113 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_113, 0, x_85);
lean_closure_set(x_113, 1, x_2);
lean_closure_set(x_113, 2, x_7);
x_114 = lean_array_fget_borrowed(x_94, x_95);
x_115 = lean_box(x_9);
x_116 = lean_box(x_10);
x_117 = lean_box(x_107);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_114);
lean_inc(x_3);
lean_inc_ref(x_6);
x_118 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_118, 0, x_85);
lean_closure_set(x_118, 1, x_6);
lean_closure_set(x_118, 2, x_8);
lean_closure_set(x_118, 3, x_115);
lean_closure_set(x_118, 4, x_116);
lean_closure_set(x_118, 5, x_7);
lean_closure_set(x_118, 6, x_11);
lean_closure_set(x_118, 7, x_16);
lean_closure_set(x_118, 8, x_3);
lean_closure_set(x_118, 9, x_114);
lean_closure_set(x_118, 10, x_12);
lean_closure_set(x_118, 11, x_13);
lean_closure_set(x_118, 12, x_14);
lean_closure_set(x_118, 13, x_15);
lean_closure_set(x_118, 14, x_113);
lean_closure_set(x_118, 15, x_117);
lean_closure_set(x_118, 16, x_2);
lean_closure_set(x_118, 17, x_61);
lean_closure_set(x_118, 18, x_60);
x_119 = lean_nat_add(x_95, x_61);
lean_dec(x_95);
lean_ctor_set(x_28, 1, x_119);
lean_inc(x_3);
x_120 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_120, 0, x_40);
lean_closure_set(x_120, 1, x_26);
lean_closure_set(x_120, 2, x_37);
lean_closure_set(x_120, 3, x_34);
lean_closure_set(x_120, 4, x_31);
lean_closure_set(x_120, 5, x_28);
lean_closure_set(x_120, 6, x_2);
lean_closure_set(x_120, 7, x_3);
x_121 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_73, x_97, x_118);
lean_inc(x_3);
x_122 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_121, x_120);
x_46 = x_122;
goto block_49;
}
}
else
{
lean_object* x_123; uint8_t x_124; uint8_t x_125; 
lean_dec(x_28);
x_123 = lean_ctor_get(x_97, 1);
x_124 = lean_ctor_get_uint8(x_97, sizeof(void*)*2);
x_125 = lean_nat_dec_eq(x_123, x_5);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_31);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_34);
lean_dec(x_85);
lean_dec_ref(x_37);
lean_dec(x_73);
lean_dec_ref(x_26);
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_126 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_127 = l_instInhabitedOfMonad___redArg(x_6, x_126);
x_128 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_129 = l_panic___redArg(x_127, x_128);
x_46 = x_129;
goto block_49;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_85);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_130, 0, x_85);
lean_closure_set(x_130, 1, x_2);
lean_closure_set(x_130, 2, x_7);
x_131 = lean_array_fget_borrowed(x_94, x_95);
x_132 = lean_box(x_9);
x_133 = lean_box(x_10);
x_134 = lean_box(x_124);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_131);
lean_inc(x_3);
lean_inc_ref(x_6);
x_135 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_135, 0, x_85);
lean_closure_set(x_135, 1, x_6);
lean_closure_set(x_135, 2, x_8);
lean_closure_set(x_135, 3, x_132);
lean_closure_set(x_135, 4, x_133);
lean_closure_set(x_135, 5, x_7);
lean_closure_set(x_135, 6, x_11);
lean_closure_set(x_135, 7, x_16);
lean_closure_set(x_135, 8, x_3);
lean_closure_set(x_135, 9, x_131);
lean_closure_set(x_135, 10, x_12);
lean_closure_set(x_135, 11, x_13);
lean_closure_set(x_135, 12, x_14);
lean_closure_set(x_135, 13, x_15);
lean_closure_set(x_135, 14, x_130);
lean_closure_set(x_135, 15, x_134);
lean_closure_set(x_135, 16, x_2);
lean_closure_set(x_135, 17, x_61);
lean_closure_set(x_135, 18, x_60);
x_136 = lean_nat_add(x_95, x_61);
lean_dec(x_95);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_94);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_96);
lean_inc(x_3);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_138, 0, x_40);
lean_closure_set(x_138, 1, x_26);
lean_closure_set(x_138, 2, x_37);
lean_closure_set(x_138, 3, x_34);
lean_closure_set(x_138, 4, x_31);
lean_closure_set(x_138, 5, x_137);
lean_closure_set(x_138, 6, x_2);
lean_closure_set(x_138, 7, x_3);
x_139 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_73, x_97, x_135);
lean_inc(x_3);
x_140 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_139, x_138);
x_46 = x_140;
goto block_49;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_31);
x_141 = lean_ctor_get(x_28, 0);
x_142 = lean_ctor_get(x_28, 1);
x_143 = lean_ctor_get(x_28, 2);
x_144 = lean_array_fget(x_82, x_83);
x_145 = lean_nat_add(x_83, x_61);
lean_dec(x_83);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_82);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_84);
x_147 = lean_nat_dec_lt(x_142, x_143);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_85);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_22, 0, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_17);
x_149 = lean_apply_2(x_2, lean_box(0), x_148);
x_46 = x_149;
goto block_49;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
lean_inc(x_143);
lean_inc(x_142);
lean_inc_ref(x_141);
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_150 = x_28;
} else {
 lean_dec_ref(x_28);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_144, 1);
x_152 = lean_ctor_get_uint8(x_144, sizeof(void*)*2);
x_153 = lean_nat_dec_eq(x_151, x_5);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_150);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_34);
lean_dec(x_85);
lean_dec_ref(x_37);
lean_dec(x_73);
lean_dec_ref(x_26);
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_154 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_155 = l_instInhabitedOfMonad___redArg(x_6, x_154);
x_156 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_157 = l_panic___redArg(x_155, x_156);
x_46 = x_157;
goto block_49;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_85);
x_158 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_158, 0, x_85);
lean_closure_set(x_158, 1, x_2);
lean_closure_set(x_158, 2, x_7);
x_159 = lean_array_fget_borrowed(x_141, x_142);
x_160 = lean_box(x_9);
x_161 = lean_box(x_10);
x_162 = lean_box(x_152);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_159);
lean_inc(x_3);
lean_inc_ref(x_6);
x_163 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_163, 0, x_85);
lean_closure_set(x_163, 1, x_6);
lean_closure_set(x_163, 2, x_8);
lean_closure_set(x_163, 3, x_160);
lean_closure_set(x_163, 4, x_161);
lean_closure_set(x_163, 5, x_7);
lean_closure_set(x_163, 6, x_11);
lean_closure_set(x_163, 7, x_16);
lean_closure_set(x_163, 8, x_3);
lean_closure_set(x_163, 9, x_159);
lean_closure_set(x_163, 10, x_12);
lean_closure_set(x_163, 11, x_13);
lean_closure_set(x_163, 12, x_14);
lean_closure_set(x_163, 13, x_15);
lean_closure_set(x_163, 14, x_158);
lean_closure_set(x_163, 15, x_162);
lean_closure_set(x_163, 16, x_2);
lean_closure_set(x_163, 17, x_61);
lean_closure_set(x_163, 18, x_60);
x_164 = lean_nat_add(x_142, x_61);
lean_dec(x_142);
if (lean_is_scalar(x_150)) {
 x_165 = lean_alloc_ctor(0, 3, 0);
} else {
 x_165 = x_150;
}
lean_ctor_set(x_165, 0, x_141);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_143);
lean_inc(x_3);
x_166 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_166, 0, x_40);
lean_closure_set(x_166, 1, x_26);
lean_closure_set(x_166, 2, x_37);
lean_closure_set(x_166, 3, x_34);
lean_closure_set(x_166, 4, x_146);
lean_closure_set(x_166, 5, x_165);
lean_closure_set(x_166, 6, x_2);
lean_closure_set(x_166, 7, x_3);
x_167 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_73, x_144, x_163);
lean_inc(x_3);
x_168 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_167, x_166);
x_46 = x_168;
goto block_49;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_34);
x_169 = lean_ctor_get(x_31, 0);
x_170 = lean_ctor_get(x_31, 1);
x_171 = lean_ctor_get(x_31, 2);
x_172 = lean_array_fget(x_70, x_71);
x_173 = lean_nat_add(x_71, x_61);
lean_dec(x_71);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_70);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set(x_174, 2, x_72);
x_175 = lean_nat_dec_lt(x_170, x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_172);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_23, 0, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_17);
x_177 = lean_apply_2(x_2, lean_box(0), x_176);
x_46 = x_177;
goto block_49;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_inc(x_171);
lean_inc(x_170);
lean_inc_ref(x_169);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_178 = x_31;
} else {
 lean_dec_ref(x_31);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_28, 0);
x_180 = lean_ctor_get(x_28, 1);
x_181 = lean_ctor_get(x_28, 2);
x_182 = lean_array_fget(x_169, x_170);
x_183 = lean_nat_add(x_170, x_61);
lean_dec(x_170);
if (lean_is_scalar(x_178)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_178;
}
lean_ctor_set(x_184, 0, x_169);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_171);
x_185 = lean_nat_dec_lt(x_180, x_181);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_182);
lean_dec(x_172);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_23, 0, x_174);
lean_ctor_set(x_22, 0, x_184);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_17);
x_187 = lean_apply_2(x_2, lean_box(0), x_186);
x_46 = x_187;
goto block_49;
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
lean_inc(x_181);
lean_inc(x_180);
lean_inc_ref(x_179);
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_188 = x_28;
} else {
 lean_dec_ref(x_28);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_182, 1);
x_190 = lean_ctor_get_uint8(x_182, sizeof(void*)*2);
x_191 = lean_nat_dec_eq(x_189, x_5);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_188);
lean_dec_ref(x_184);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_174);
lean_dec(x_172);
lean_dec_ref(x_37);
lean_dec(x_73);
lean_dec_ref(x_26);
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_192 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_193 = l_instInhabitedOfMonad___redArg(x_6, x_192);
x_194 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_195 = l_panic___redArg(x_193, x_194);
x_46 = x_195;
goto block_49;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_172);
x_196 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_196, 0, x_172);
lean_closure_set(x_196, 1, x_2);
lean_closure_set(x_196, 2, x_7);
x_197 = lean_array_fget_borrowed(x_179, x_180);
x_198 = lean_box(x_9);
x_199 = lean_box(x_10);
x_200 = lean_box(x_190);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_197);
lean_inc(x_3);
lean_inc_ref(x_6);
x_201 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_201, 0, x_172);
lean_closure_set(x_201, 1, x_6);
lean_closure_set(x_201, 2, x_8);
lean_closure_set(x_201, 3, x_198);
lean_closure_set(x_201, 4, x_199);
lean_closure_set(x_201, 5, x_7);
lean_closure_set(x_201, 6, x_11);
lean_closure_set(x_201, 7, x_16);
lean_closure_set(x_201, 8, x_3);
lean_closure_set(x_201, 9, x_197);
lean_closure_set(x_201, 10, x_12);
lean_closure_set(x_201, 11, x_13);
lean_closure_set(x_201, 12, x_14);
lean_closure_set(x_201, 13, x_15);
lean_closure_set(x_201, 14, x_196);
lean_closure_set(x_201, 15, x_200);
lean_closure_set(x_201, 16, x_2);
lean_closure_set(x_201, 17, x_61);
lean_closure_set(x_201, 18, x_60);
x_202 = lean_nat_add(x_180, x_61);
lean_dec(x_180);
if (lean_is_scalar(x_188)) {
 x_203 = lean_alloc_ctor(0, 3, 0);
} else {
 x_203 = x_188;
}
lean_ctor_set(x_203, 0, x_179);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_203, 2, x_181);
lean_inc(x_3);
x_204 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_204, 0, x_40);
lean_closure_set(x_204, 1, x_26);
lean_closure_set(x_204, 2, x_37);
lean_closure_set(x_204, 3, x_174);
lean_closure_set(x_204, 4, x_184);
lean_closure_set(x_204, 5, x_203);
lean_closure_set(x_204, 6, x_2);
lean_closure_set(x_204, 7, x_3);
x_205 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_73, x_182, x_201);
lean_inc(x_3);
x_206 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_205, x_204);
x_46 = x_206;
goto block_49;
}
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_37);
x_207 = lean_ctor_get(x_34, 0);
x_208 = lean_ctor_get(x_34, 1);
x_209 = lean_ctor_get(x_34, 2);
x_210 = lean_array_fget(x_57, x_58);
x_211 = lean_nat_add(x_58, x_61);
lean_dec(x_58);
x_212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_212, 0, x_57);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_59);
x_213 = lean_nat_dec_lt(x_208, x_209);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_210);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_24, 0, x_212);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_17);
x_215 = lean_apply_2(x_2, lean_box(0), x_214);
x_46 = x_215;
goto block_49;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_inc(x_209);
lean_inc(x_208);
lean_inc_ref(x_207);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_216 = x_34;
} else {
 lean_dec_ref(x_34);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_31, 0);
x_218 = lean_ctor_get(x_31, 1);
x_219 = lean_ctor_get(x_31, 2);
x_220 = lean_array_fget(x_207, x_208);
x_221 = lean_nat_add(x_208, x_61);
lean_dec(x_208);
if (lean_is_scalar(x_216)) {
 x_222 = lean_alloc_ctor(0, 3, 0);
} else {
 x_222 = x_216;
}
lean_ctor_set(x_222, 0, x_207);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set(x_222, 2, x_209);
x_223 = lean_nat_dec_lt(x_218, x_219);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_220);
lean_dec(x_210);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_24, 0, x_212);
lean_ctor_set(x_23, 0, x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_17);
x_225 = lean_apply_2(x_2, lean_box(0), x_224);
x_46 = x_225;
goto block_49;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_inc(x_219);
lean_inc(x_218);
lean_inc_ref(x_217);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_226 = x_31;
} else {
 lean_dec_ref(x_31);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_28, 0);
x_228 = lean_ctor_get(x_28, 1);
x_229 = lean_ctor_get(x_28, 2);
x_230 = lean_array_fget(x_217, x_218);
x_231 = lean_nat_add(x_218, x_61);
lean_dec(x_218);
if (lean_is_scalar(x_226)) {
 x_232 = lean_alloc_ctor(0, 3, 0);
} else {
 x_232 = x_226;
}
lean_ctor_set(x_232, 0, x_217);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_219);
x_233 = lean_nat_dec_lt(x_228, x_229);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_230);
lean_dec(x_220);
lean_dec(x_210);
lean_dec(x_60);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_24, 0, x_212);
lean_ctor_set(x_23, 0, x_222);
lean_ctor_set(x_22, 0, x_232);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_17);
x_235 = lean_apply_2(x_2, lean_box(0), x_234);
x_46 = x_235;
goto block_49;
}
else
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_239; 
lean_inc(x_229);
lean_inc(x_228);
lean_inc_ref(x_227);
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_236 = x_28;
} else {
 lean_dec_ref(x_28);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_230, 1);
x_238 = lean_ctor_get_uint8(x_230, sizeof(void*)*2);
x_239 = lean_nat_dec_eq(x_237, x_5);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_236);
lean_dec_ref(x_232);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_212);
lean_dec(x_210);
lean_dec_ref(x_26);
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_240 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_241 = l_instInhabitedOfMonad___redArg(x_6, x_240);
x_242 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_243 = l_panic___redArg(x_241, x_242);
x_46 = x_243;
goto block_49;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_220);
x_244 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_244, 0, x_220);
lean_closure_set(x_244, 1, x_2);
lean_closure_set(x_244, 2, x_7);
x_245 = lean_array_fget_borrowed(x_227, x_228);
x_246 = lean_box(x_9);
x_247 = lean_box(x_10);
x_248 = lean_box(x_238);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_245);
lean_inc(x_3);
lean_inc_ref(x_6);
x_249 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_249, 0, x_220);
lean_closure_set(x_249, 1, x_6);
lean_closure_set(x_249, 2, x_8);
lean_closure_set(x_249, 3, x_246);
lean_closure_set(x_249, 4, x_247);
lean_closure_set(x_249, 5, x_7);
lean_closure_set(x_249, 6, x_11);
lean_closure_set(x_249, 7, x_16);
lean_closure_set(x_249, 8, x_3);
lean_closure_set(x_249, 9, x_245);
lean_closure_set(x_249, 10, x_12);
lean_closure_set(x_249, 11, x_13);
lean_closure_set(x_249, 12, x_14);
lean_closure_set(x_249, 13, x_15);
lean_closure_set(x_249, 14, x_244);
lean_closure_set(x_249, 15, x_248);
lean_closure_set(x_249, 16, x_2);
lean_closure_set(x_249, 17, x_61);
lean_closure_set(x_249, 18, x_60);
x_250 = lean_nat_add(x_228, x_61);
lean_dec(x_228);
if (lean_is_scalar(x_236)) {
 x_251 = lean_alloc_ctor(0, 3, 0);
} else {
 x_251 = x_236;
}
lean_ctor_set(x_251, 0, x_227);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_229);
lean_inc(x_3);
x_252 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_252, 0, x_40);
lean_closure_set(x_252, 1, x_26);
lean_closure_set(x_252, 2, x_212);
lean_closure_set(x_252, 3, x_222);
lean_closure_set(x_252, 4, x_232);
lean_closure_set(x_252, 5, x_251);
lean_closure_set(x_252, 6, x_2);
lean_closure_set(x_252, 7, x_3);
x_253 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_210, x_230, x_249);
lean_inc(x_3);
x_254 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_253, x_252);
x_46 = x_254;
goto block_49;
}
}
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
lean_dec(x_26);
x_255 = lean_ctor_get(x_37, 0);
x_256 = lean_ctor_get(x_37, 1);
x_257 = lean_ctor_get(x_37, 2);
x_258 = lean_array_fget(x_42, x_43);
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_43, x_259);
lean_dec(x_43);
x_261 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_261, 0, x_42);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set(x_261, 2, x_44);
x_262 = lean_nat_dec_lt(x_256, x_257);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_258);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_25, 0, x_261);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_17);
x_264 = lean_apply_2(x_2, lean_box(0), x_263);
x_46 = x_264;
goto block_49;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_inc(x_257);
lean_inc(x_256);
lean_inc_ref(x_255);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_265 = x_37;
} else {
 lean_dec_ref(x_37);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_34, 0);
x_267 = lean_ctor_get(x_34, 1);
x_268 = lean_ctor_get(x_34, 2);
x_269 = lean_array_fget(x_255, x_256);
x_270 = lean_nat_add(x_256, x_259);
lean_dec(x_256);
if (lean_is_scalar(x_265)) {
 x_271 = lean_alloc_ctor(0, 3, 0);
} else {
 x_271 = x_265;
}
lean_ctor_set(x_271, 0, x_255);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set(x_271, 2, x_257);
x_272 = lean_nat_dec_lt(x_267, x_268);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_25, 0, x_261);
lean_ctor_set(x_24, 0, x_271);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_17);
x_274 = lean_apply_2(x_2, lean_box(0), x_273);
x_46 = x_274;
goto block_49;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_inc(x_268);
lean_inc(x_267);
lean_inc_ref(x_266);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_275 = x_34;
} else {
 lean_dec_ref(x_34);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_31, 0);
x_277 = lean_ctor_get(x_31, 1);
x_278 = lean_ctor_get(x_31, 2);
x_279 = lean_array_fget(x_266, x_267);
x_280 = lean_nat_add(x_267, x_259);
lean_dec(x_267);
if (lean_is_scalar(x_275)) {
 x_281 = lean_alloc_ctor(0, 3, 0);
} else {
 x_281 = x_275;
}
lean_ctor_set(x_281, 0, x_266);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_268);
x_282 = lean_nat_dec_lt(x_277, x_278);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_279);
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_25, 0, x_261);
lean_ctor_set(x_24, 0, x_271);
lean_ctor_set(x_23, 0, x_281);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_17);
x_284 = lean_apply_2(x_2, lean_box(0), x_283);
x_46 = x_284;
goto block_49;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
lean_inc(x_278);
lean_inc(x_277);
lean_inc_ref(x_276);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_285 = x_31;
} else {
 lean_dec_ref(x_31);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_28, 0);
x_287 = lean_ctor_get(x_28, 1);
x_288 = lean_ctor_get(x_28, 2);
x_289 = lean_array_fget(x_276, x_277);
x_290 = lean_nat_add(x_277, x_259);
lean_dec(x_277);
if (lean_is_scalar(x_285)) {
 x_291 = lean_alloc_ctor(0, 3, 0);
} else {
 x_291 = x_285;
}
lean_ctor_set(x_291, 0, x_276);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_291, 2, x_278);
x_292 = lean_nat_dec_lt(x_287, x_288);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_289);
lean_dec(x_279);
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_25, 0, x_261);
lean_ctor_set(x_24, 0, x_271);
lean_ctor_set(x_23, 0, x_281);
lean_ctor_set(x_22, 0, x_291);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_17);
x_294 = lean_apply_2(x_2, lean_box(0), x_293);
x_46 = x_294;
goto block_49;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_298; 
lean_inc(x_288);
lean_inc(x_287);
lean_inc_ref(x_286);
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_295 = x_28;
} else {
 lean_dec_ref(x_28);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_289, 1);
x_297 = lean_ctor_get_uint8(x_289, sizeof(void*)*2);
x_298 = lean_nat_dec_eq(x_296, x_5);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_295);
lean_dec_ref(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_281);
lean_dec(x_279);
lean_dec_ref(x_271);
lean_dec(x_269);
lean_dec_ref(x_261);
lean_dec(x_258);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_299 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_300 = l_instInhabitedOfMonad___redArg(x_6, x_299);
x_301 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_302 = l_panic___redArg(x_300, x_301);
x_46 = x_302;
goto block_49;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_279);
x_303 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_303, 0, x_279);
lean_closure_set(x_303, 1, x_2);
lean_closure_set(x_303, 2, x_7);
x_304 = lean_array_fget_borrowed(x_286, x_287);
x_305 = lean_box(x_9);
x_306 = lean_box(x_10);
x_307 = lean_box(x_297);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_304);
lean_inc(x_3);
lean_inc_ref(x_6);
x_308 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_308, 0, x_279);
lean_closure_set(x_308, 1, x_6);
lean_closure_set(x_308, 2, x_8);
lean_closure_set(x_308, 3, x_305);
lean_closure_set(x_308, 4, x_306);
lean_closure_set(x_308, 5, x_7);
lean_closure_set(x_308, 6, x_11);
lean_closure_set(x_308, 7, x_16);
lean_closure_set(x_308, 8, x_3);
lean_closure_set(x_308, 9, x_304);
lean_closure_set(x_308, 10, x_12);
lean_closure_set(x_308, 11, x_13);
lean_closure_set(x_308, 12, x_14);
lean_closure_set(x_308, 13, x_15);
lean_closure_set(x_308, 14, x_303);
lean_closure_set(x_308, 15, x_307);
lean_closure_set(x_308, 16, x_2);
lean_closure_set(x_308, 17, x_259);
lean_closure_set(x_308, 18, x_258);
x_309 = lean_nat_add(x_287, x_259);
lean_dec(x_287);
if (lean_is_scalar(x_295)) {
 x_310 = lean_alloc_ctor(0, 3, 0);
} else {
 x_310 = x_295;
}
lean_ctor_set(x_310, 0, x_286);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set(x_310, 2, x_288);
lean_inc(x_3);
x_311 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_311, 0, x_40);
lean_closure_set(x_311, 1, x_261);
lean_closure_set(x_311, 2, x_271);
lean_closure_set(x_311, 3, x_281);
lean_closure_set(x_311, 4, x_291);
lean_closure_set(x_311, 5, x_310);
lean_closure_set(x_311, 6, x_2);
lean_closure_set(x_311, 7, x_3);
x_312 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_269, x_289, x_308);
lean_inc(x_3);
x_313 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_312, x_311);
x_46 = x_313;
goto block_49;
}
}
}
}
}
}
}
block_49:
{
lean_object* x_47; lean_object* x_48; 
lean_inc(x_3);
x_47 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_46, x_4);
x_48 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_47, x_45);
return x_48;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_323; 
x_314 = lean_ctor_get(x_25, 1);
lean_inc(x_314);
lean_dec(x_25);
x_315 = lean_ctor_get(x_26, 0);
x_316 = lean_ctor_get(x_26, 1);
x_317 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_318 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_318, 0, x_2);
lean_closure_set(x_318, 1, x_16);
lean_closure_set(x_318, 2, x_19);
x_323 = lean_nat_dec_lt(x_316, x_317);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_26);
lean_ctor_set(x_324, 1, x_314);
lean_ctor_set(x_24, 1, x_324);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_17);
x_326 = lean_apply_2(x_2, lean_box(0), x_325);
x_319 = x_326;
goto block_322;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_inc(x_317);
lean_inc(x_316);
lean_inc_ref(x_315);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_327 = x_26;
} else {
 lean_dec_ref(x_26);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_37, 0);
x_329 = lean_ctor_get(x_37, 1);
x_330 = lean_ctor_get(x_37, 2);
x_331 = lean_array_fget(x_315, x_316);
x_332 = lean_unsigned_to_nat(1u);
x_333 = lean_nat_add(x_316, x_332);
lean_dec(x_316);
if (lean_is_scalar(x_327)) {
 x_334 = lean_alloc_ctor(0, 3, 0);
} else {
 x_334 = x_327;
}
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_334, 2, x_317);
x_335 = lean_nat_dec_lt(x_329, x_330);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_331);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_314);
lean_ctor_set(x_24, 1, x_336);
x_337 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_337, 0, x_17);
x_338 = lean_apply_2(x_2, lean_box(0), x_337);
x_319 = x_338;
goto block_322;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
lean_inc(x_330);
lean_inc(x_329);
lean_inc_ref(x_328);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_339 = x_37;
} else {
 lean_dec_ref(x_37);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_34, 0);
x_341 = lean_ctor_get(x_34, 1);
x_342 = lean_ctor_get(x_34, 2);
x_343 = lean_array_fget(x_328, x_329);
x_344 = lean_nat_add(x_329, x_332);
lean_dec(x_329);
if (lean_is_scalar(x_339)) {
 x_345 = lean_alloc_ctor(0, 3, 0);
} else {
 x_345 = x_339;
}
lean_ctor_set(x_345, 0, x_328);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_345, 2, x_330);
x_346 = lean_nat_dec_lt(x_341, x_342);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_343);
lean_dec(x_331);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_334);
lean_ctor_set(x_347, 1, x_314);
lean_ctor_set(x_24, 1, x_347);
lean_ctor_set(x_24, 0, x_345);
x_348 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_348, 0, x_17);
x_349 = lean_apply_2(x_2, lean_box(0), x_348);
x_319 = x_349;
goto block_322;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
lean_inc(x_342);
lean_inc(x_341);
lean_inc_ref(x_340);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_350 = x_34;
} else {
 lean_dec_ref(x_34);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_31, 0);
x_352 = lean_ctor_get(x_31, 1);
x_353 = lean_ctor_get(x_31, 2);
x_354 = lean_array_fget(x_340, x_341);
x_355 = lean_nat_add(x_341, x_332);
lean_dec(x_341);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(0, 3, 0);
} else {
 x_356 = x_350;
}
lean_ctor_set(x_356, 0, x_340);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set(x_356, 2, x_342);
x_357 = lean_nat_dec_lt(x_352, x_353);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_354);
lean_dec(x_343);
lean_dec(x_331);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_334);
lean_ctor_set(x_358, 1, x_314);
lean_ctor_set(x_24, 1, x_358);
lean_ctor_set(x_24, 0, x_345);
lean_ctor_set(x_23, 0, x_356);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_17);
x_360 = lean_apply_2(x_2, lean_box(0), x_359);
x_319 = x_360;
goto block_322;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_inc(x_353);
lean_inc(x_352);
lean_inc_ref(x_351);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_361 = x_31;
} else {
 lean_dec_ref(x_31);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_28, 0);
x_363 = lean_ctor_get(x_28, 1);
x_364 = lean_ctor_get(x_28, 2);
x_365 = lean_array_fget(x_351, x_352);
x_366 = lean_nat_add(x_352, x_332);
lean_dec(x_352);
if (lean_is_scalar(x_361)) {
 x_367 = lean_alloc_ctor(0, 3, 0);
} else {
 x_367 = x_361;
}
lean_ctor_set(x_367, 0, x_351);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set(x_367, 2, x_353);
x_368 = lean_nat_dec_lt(x_363, x_364);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_365);
lean_dec(x_354);
lean_dec(x_343);
lean_dec(x_331);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_334);
lean_ctor_set(x_369, 1, x_314);
lean_ctor_set(x_24, 1, x_369);
lean_ctor_set(x_24, 0, x_345);
lean_ctor_set(x_23, 0, x_356);
lean_ctor_set(x_22, 0, x_367);
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_17);
x_371 = lean_apply_2(x_2, lean_box(0), x_370);
x_319 = x_371;
goto block_322;
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_375; 
lean_inc(x_364);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_372 = x_28;
} else {
 lean_dec_ref(x_28);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_365, 1);
x_374 = lean_ctor_get_uint8(x_365, sizeof(void*)*2);
x_375 = lean_nat_dec_eq(x_373, x_5);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_372);
lean_dec_ref(x_367);
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec_ref(x_345);
lean_dec(x_343);
lean_dec_ref(x_334);
lean_dec(x_331);
lean_dec(x_314);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_376 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_377 = l_instInhabitedOfMonad___redArg(x_6, x_376);
x_378 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_379 = l_panic___redArg(x_377, x_378);
x_319 = x_379;
goto block_322;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_354);
x_380 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_380, 0, x_354);
lean_closure_set(x_380, 1, x_2);
lean_closure_set(x_380, 2, x_7);
x_381 = lean_array_fget_borrowed(x_362, x_363);
x_382 = lean_box(x_9);
x_383 = lean_box(x_10);
x_384 = lean_box(x_374);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_381);
lean_inc(x_3);
lean_inc_ref(x_6);
x_385 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_385, 0, x_354);
lean_closure_set(x_385, 1, x_6);
lean_closure_set(x_385, 2, x_8);
lean_closure_set(x_385, 3, x_382);
lean_closure_set(x_385, 4, x_383);
lean_closure_set(x_385, 5, x_7);
lean_closure_set(x_385, 6, x_11);
lean_closure_set(x_385, 7, x_16);
lean_closure_set(x_385, 8, x_3);
lean_closure_set(x_385, 9, x_381);
lean_closure_set(x_385, 10, x_12);
lean_closure_set(x_385, 11, x_13);
lean_closure_set(x_385, 12, x_14);
lean_closure_set(x_385, 13, x_15);
lean_closure_set(x_385, 14, x_380);
lean_closure_set(x_385, 15, x_384);
lean_closure_set(x_385, 16, x_2);
lean_closure_set(x_385, 17, x_332);
lean_closure_set(x_385, 18, x_331);
x_386 = lean_nat_add(x_363, x_332);
lean_dec(x_363);
if (lean_is_scalar(x_372)) {
 x_387 = lean_alloc_ctor(0, 3, 0);
} else {
 x_387 = x_372;
}
lean_ctor_set(x_387, 0, x_362);
lean_ctor_set(x_387, 1, x_386);
lean_ctor_set(x_387, 2, x_364);
lean_inc(x_3);
x_388 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_388, 0, x_314);
lean_closure_set(x_388, 1, x_334);
lean_closure_set(x_388, 2, x_345);
lean_closure_set(x_388, 3, x_356);
lean_closure_set(x_388, 4, x_367);
lean_closure_set(x_388, 5, x_387);
lean_closure_set(x_388, 6, x_2);
lean_closure_set(x_388, 7, x_3);
x_389 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_343, x_365, x_385);
lean_inc(x_3);
x_390 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_389, x_388);
x_319 = x_390;
goto block_322;
}
}
}
}
}
}
block_322:
{
lean_object* x_320; lean_object* x_321; 
lean_inc(x_3);
x_320 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_319, x_4);
x_321 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_320, x_318);
return x_321;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_402; 
x_391 = lean_ctor_get(x_24, 0);
lean_inc(x_391);
lean_dec(x_24);
x_392 = lean_ctor_get(x_25, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_393 = x_25;
} else {
 lean_dec_ref(x_25);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_26, 0);
x_395 = lean_ctor_get(x_26, 1);
x_396 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_397 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_397, 0, x_2);
lean_closure_set(x_397, 1, x_16);
lean_closure_set(x_397, 2, x_19);
x_402 = lean_nat_dec_lt(x_395, x_396);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_393)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_393;
}
lean_ctor_set(x_403, 0, x_26);
lean_ctor_set(x_403, 1, x_392);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_391);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_23, 1, x_404);
x_405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_405, 0, x_17);
x_406 = lean_apply_2(x_2, lean_box(0), x_405);
x_398 = x_406;
goto block_401;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_inc(x_396);
lean_inc(x_395);
lean_inc_ref(x_394);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_407 = x_26;
} else {
 lean_dec_ref(x_26);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_391, 0);
x_409 = lean_ctor_get(x_391, 1);
x_410 = lean_ctor_get(x_391, 2);
x_411 = lean_array_fget(x_394, x_395);
x_412 = lean_unsigned_to_nat(1u);
x_413 = lean_nat_add(x_395, x_412);
lean_dec(x_395);
if (lean_is_scalar(x_407)) {
 x_414 = lean_alloc_ctor(0, 3, 0);
} else {
 x_414 = x_407;
}
lean_ctor_set(x_414, 0, x_394);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set(x_414, 2, x_396);
x_415 = lean_nat_dec_lt(x_409, x_410);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_411);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_393)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_393;
}
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_392);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_391);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set(x_23, 1, x_417);
x_418 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_418, 0, x_17);
x_419 = lean_apply_2(x_2, lean_box(0), x_418);
x_398 = x_419;
goto block_401;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_inc(x_410);
lean_inc(x_409);
lean_inc_ref(x_408);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 lean_ctor_release(x_391, 2);
 x_420 = x_391;
} else {
 lean_dec_ref(x_391);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_34, 0);
x_422 = lean_ctor_get(x_34, 1);
x_423 = lean_ctor_get(x_34, 2);
x_424 = lean_array_fget(x_408, x_409);
x_425 = lean_nat_add(x_409, x_412);
lean_dec(x_409);
if (lean_is_scalar(x_420)) {
 x_426 = lean_alloc_ctor(0, 3, 0);
} else {
 x_426 = x_420;
}
lean_ctor_set(x_426, 0, x_408);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set(x_426, 2, x_410);
x_427 = lean_nat_dec_lt(x_422, x_423);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_424);
lean_dec(x_411);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_393)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_393;
}
lean_ctor_set(x_428, 0, x_414);
lean_ctor_set(x_428, 1, x_392);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set(x_23, 1, x_429);
x_430 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_430, 0, x_17);
x_431 = lean_apply_2(x_2, lean_box(0), x_430);
x_398 = x_431;
goto block_401;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_inc(x_423);
lean_inc(x_422);
lean_inc_ref(x_421);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_432 = x_34;
} else {
 lean_dec_ref(x_34);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_31, 0);
x_434 = lean_ctor_get(x_31, 1);
x_435 = lean_ctor_get(x_31, 2);
x_436 = lean_array_fget(x_421, x_422);
x_437 = lean_nat_add(x_422, x_412);
lean_dec(x_422);
if (lean_is_scalar(x_432)) {
 x_438 = lean_alloc_ctor(0, 3, 0);
} else {
 x_438 = x_432;
}
lean_ctor_set(x_438, 0, x_421);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set(x_438, 2, x_423);
x_439 = lean_nat_dec_lt(x_434, x_435);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_436);
lean_dec(x_424);
lean_dec(x_411);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_393)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_393;
}
lean_ctor_set(x_440, 0, x_414);
lean_ctor_set(x_440, 1, x_392);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_426);
lean_ctor_set(x_441, 1, x_440);
lean_ctor_set(x_23, 1, x_441);
lean_ctor_set(x_23, 0, x_438);
x_442 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_442, 0, x_17);
x_443 = lean_apply_2(x_2, lean_box(0), x_442);
x_398 = x_443;
goto block_401;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_inc(x_435);
lean_inc(x_434);
lean_inc_ref(x_433);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_444 = x_31;
} else {
 lean_dec_ref(x_31);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_28, 0);
x_446 = lean_ctor_get(x_28, 1);
x_447 = lean_ctor_get(x_28, 2);
x_448 = lean_array_fget(x_433, x_434);
x_449 = lean_nat_add(x_434, x_412);
lean_dec(x_434);
if (lean_is_scalar(x_444)) {
 x_450 = lean_alloc_ctor(0, 3, 0);
} else {
 x_450 = x_444;
}
lean_ctor_set(x_450, 0, x_433);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_435);
x_451 = lean_nat_dec_lt(x_446, x_447);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_448);
lean_dec(x_436);
lean_dec(x_424);
lean_dec(x_411);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_393)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_393;
}
lean_ctor_set(x_452, 0, x_414);
lean_ctor_set(x_452, 1, x_392);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_426);
lean_ctor_set(x_453, 1, x_452);
lean_ctor_set(x_23, 1, x_453);
lean_ctor_set(x_23, 0, x_438);
lean_ctor_set(x_22, 0, x_450);
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_17);
x_455 = lean_apply_2(x_2, lean_box(0), x_454);
x_398 = x_455;
goto block_401;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; 
lean_inc(x_447);
lean_inc(x_446);
lean_inc_ref(x_445);
lean_dec(x_393);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_456 = x_28;
} else {
 lean_dec_ref(x_28);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_448, 1);
x_458 = lean_ctor_get_uint8(x_448, sizeof(void*)*2);
x_459 = lean_nat_dec_eq(x_457, x_5);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_456);
lean_dec_ref(x_450);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec_ref(x_438);
lean_dec(x_436);
lean_dec_ref(x_426);
lean_dec(x_424);
lean_dec_ref(x_414);
lean_dec(x_411);
lean_dec(x_392);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_460 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_461 = l_instInhabitedOfMonad___redArg(x_6, x_460);
x_462 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_463 = l_panic___redArg(x_461, x_462);
x_398 = x_463;
goto block_401;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_436);
x_464 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_464, 0, x_436);
lean_closure_set(x_464, 1, x_2);
lean_closure_set(x_464, 2, x_7);
x_465 = lean_array_fget_borrowed(x_445, x_446);
x_466 = lean_box(x_9);
x_467 = lean_box(x_10);
x_468 = lean_box(x_458);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_465);
lean_inc(x_3);
lean_inc_ref(x_6);
x_469 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_469, 0, x_436);
lean_closure_set(x_469, 1, x_6);
lean_closure_set(x_469, 2, x_8);
lean_closure_set(x_469, 3, x_466);
lean_closure_set(x_469, 4, x_467);
lean_closure_set(x_469, 5, x_7);
lean_closure_set(x_469, 6, x_11);
lean_closure_set(x_469, 7, x_16);
lean_closure_set(x_469, 8, x_3);
lean_closure_set(x_469, 9, x_465);
lean_closure_set(x_469, 10, x_12);
lean_closure_set(x_469, 11, x_13);
lean_closure_set(x_469, 12, x_14);
lean_closure_set(x_469, 13, x_15);
lean_closure_set(x_469, 14, x_464);
lean_closure_set(x_469, 15, x_468);
lean_closure_set(x_469, 16, x_2);
lean_closure_set(x_469, 17, x_412);
lean_closure_set(x_469, 18, x_411);
x_470 = lean_nat_add(x_446, x_412);
lean_dec(x_446);
if (lean_is_scalar(x_456)) {
 x_471 = lean_alloc_ctor(0, 3, 0);
} else {
 x_471 = x_456;
}
lean_ctor_set(x_471, 0, x_445);
lean_ctor_set(x_471, 1, x_470);
lean_ctor_set(x_471, 2, x_447);
lean_inc(x_3);
x_472 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_472, 0, x_392);
lean_closure_set(x_472, 1, x_414);
lean_closure_set(x_472, 2, x_426);
lean_closure_set(x_472, 3, x_438);
lean_closure_set(x_472, 4, x_450);
lean_closure_set(x_472, 5, x_471);
lean_closure_set(x_472, 6, x_2);
lean_closure_set(x_472, 7, x_3);
x_473 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_424, x_448, x_469);
lean_inc(x_3);
x_474 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_473, x_472);
x_398 = x_474;
goto block_401;
}
}
}
}
}
}
block_401:
{
lean_object* x_399; lean_object* x_400; 
lean_inc(x_3);
x_399 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_398, x_4);
x_400 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_399, x_397);
return x_400;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_488; 
x_475 = lean_ctor_get(x_23, 0);
lean_inc(x_475);
lean_dec(x_23);
x_476 = lean_ctor_get(x_24, 0);
lean_inc(x_476);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_477 = x_24;
} else {
 lean_dec_ref(x_24);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_25, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_479 = x_25;
} else {
 lean_dec_ref(x_25);
 x_479 = lean_box(0);
}
x_480 = lean_ctor_get(x_26, 0);
x_481 = lean_ctor_get(x_26, 1);
x_482 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_483 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_483, 0, x_2);
lean_closure_set(x_483, 1, x_16);
lean_closure_set(x_483, 2, x_19);
x_488 = lean_nat_dec_lt(x_481, x_482);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_479)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_479;
}
lean_ctor_set(x_489, 0, x_26);
lean_ctor_set(x_489, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_477;
}
lean_ctor_set(x_490, 0, x_476);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_491, 0, x_475);
lean_ctor_set(x_491, 1, x_490);
lean_ctor_set(x_22, 1, x_491);
x_492 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_492, 0, x_17);
x_493 = lean_apply_2(x_2, lean_box(0), x_492);
x_484 = x_493;
goto block_487;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
lean_inc(x_482);
lean_inc(x_481);
lean_inc_ref(x_480);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_494 = x_26;
} else {
 lean_dec_ref(x_26);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_476, 0);
x_496 = lean_ctor_get(x_476, 1);
x_497 = lean_ctor_get(x_476, 2);
x_498 = lean_array_fget(x_480, x_481);
x_499 = lean_unsigned_to_nat(1u);
x_500 = lean_nat_add(x_481, x_499);
lean_dec(x_481);
if (lean_is_scalar(x_494)) {
 x_501 = lean_alloc_ctor(0, 3, 0);
} else {
 x_501 = x_494;
}
lean_ctor_set(x_501, 0, x_480);
lean_ctor_set(x_501, 1, x_500);
lean_ctor_set(x_501, 2, x_482);
x_502 = lean_nat_dec_lt(x_496, x_497);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_498);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_479)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_479;
}
lean_ctor_set(x_503, 0, x_501);
lean_ctor_set(x_503, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_477;
}
lean_ctor_set(x_504, 0, x_476);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_475);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_22, 1, x_505);
x_506 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_506, 0, x_17);
x_507 = lean_apply_2(x_2, lean_box(0), x_506);
x_484 = x_507;
goto block_487;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
lean_inc(x_497);
lean_inc(x_496);
lean_inc_ref(x_495);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 x_508 = x_476;
} else {
 lean_dec_ref(x_476);
 x_508 = lean_box(0);
}
x_509 = lean_ctor_get(x_475, 0);
x_510 = lean_ctor_get(x_475, 1);
x_511 = lean_ctor_get(x_475, 2);
x_512 = lean_array_fget(x_495, x_496);
x_513 = lean_nat_add(x_496, x_499);
lean_dec(x_496);
if (lean_is_scalar(x_508)) {
 x_514 = lean_alloc_ctor(0, 3, 0);
} else {
 x_514 = x_508;
}
lean_ctor_set(x_514, 0, x_495);
lean_ctor_set(x_514, 1, x_513);
lean_ctor_set(x_514, 2, x_497);
x_515 = lean_nat_dec_lt(x_510, x_511);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_512);
lean_dec(x_498);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_479)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_479;
}
lean_ctor_set(x_516, 0, x_501);
lean_ctor_set(x_516, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_477;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_475);
lean_ctor_set(x_518, 1, x_517);
lean_ctor_set(x_22, 1, x_518);
x_519 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_519, 0, x_17);
x_520 = lean_apply_2(x_2, lean_box(0), x_519);
x_484 = x_520;
goto block_487;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; 
lean_inc(x_511);
lean_inc(x_510);
lean_inc_ref(x_509);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 x_521 = x_475;
} else {
 lean_dec_ref(x_475);
 x_521 = lean_box(0);
}
x_522 = lean_ctor_get(x_31, 0);
x_523 = lean_ctor_get(x_31, 1);
x_524 = lean_ctor_get(x_31, 2);
x_525 = lean_array_fget(x_509, x_510);
x_526 = lean_nat_add(x_510, x_499);
lean_dec(x_510);
if (lean_is_scalar(x_521)) {
 x_527 = lean_alloc_ctor(0, 3, 0);
} else {
 x_527 = x_521;
}
lean_ctor_set(x_527, 0, x_509);
lean_ctor_set(x_527, 1, x_526);
lean_ctor_set(x_527, 2, x_511);
x_528 = lean_nat_dec_lt(x_523, x_524);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_525);
lean_dec(x_512);
lean_dec(x_498);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_479)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_479;
}
lean_ctor_set(x_529, 0, x_501);
lean_ctor_set(x_529, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_477;
}
lean_ctor_set(x_530, 0, x_514);
lean_ctor_set(x_530, 1, x_529);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_22, 1, x_531);
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_17);
x_533 = lean_apply_2(x_2, lean_box(0), x_532);
x_484 = x_533;
goto block_487;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
lean_inc(x_524);
lean_inc(x_523);
lean_inc_ref(x_522);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_534 = x_31;
} else {
 lean_dec_ref(x_31);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_28, 0);
x_536 = lean_ctor_get(x_28, 1);
x_537 = lean_ctor_get(x_28, 2);
x_538 = lean_array_fget(x_522, x_523);
x_539 = lean_nat_add(x_523, x_499);
lean_dec(x_523);
if (lean_is_scalar(x_534)) {
 x_540 = lean_alloc_ctor(0, 3, 0);
} else {
 x_540 = x_534;
}
lean_ctor_set(x_540, 0, x_522);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set(x_540, 2, x_524);
x_541 = lean_nat_dec_lt(x_536, x_537);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_538);
lean_dec(x_525);
lean_dec(x_512);
lean_dec(x_498);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_479)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_479;
}
lean_ctor_set(x_542, 0, x_501);
lean_ctor_set(x_542, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_477;
}
lean_ctor_set(x_543, 0, x_514);
lean_ctor_set(x_543, 1, x_542);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_527);
lean_ctor_set(x_544, 1, x_543);
lean_ctor_set(x_22, 1, x_544);
lean_ctor_set(x_22, 0, x_540);
x_545 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_545, 0, x_17);
x_546 = lean_apply_2(x_2, lean_box(0), x_545);
x_484 = x_546;
goto block_487;
}
else
{
lean_object* x_547; lean_object* x_548; uint8_t x_549; uint8_t x_550; 
lean_inc(x_537);
lean_inc(x_536);
lean_inc_ref(x_535);
lean_dec(x_479);
lean_dec(x_477);
lean_free_object(x_22);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_547 = x_28;
} else {
 lean_dec_ref(x_28);
 x_547 = lean_box(0);
}
x_548 = lean_ctor_get(x_538, 1);
x_549 = lean_ctor_get_uint8(x_538, sizeof(void*)*2);
x_550 = lean_nat_dec_eq(x_548, x_5);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_547);
lean_dec_ref(x_540);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec_ref(x_535);
lean_dec_ref(x_527);
lean_dec(x_525);
lean_dec_ref(x_514);
lean_dec(x_512);
lean_dec_ref(x_501);
lean_dec(x_498);
lean_dec(x_478);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_551 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_552 = l_instInhabitedOfMonad___redArg(x_6, x_551);
x_553 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_554 = l_panic___redArg(x_552, x_553);
x_484 = x_554;
goto block_487;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_525);
x_555 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_555, 0, x_525);
lean_closure_set(x_555, 1, x_2);
lean_closure_set(x_555, 2, x_7);
x_556 = lean_array_fget_borrowed(x_535, x_536);
x_557 = lean_box(x_9);
x_558 = lean_box(x_10);
x_559 = lean_box(x_549);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_556);
lean_inc(x_3);
lean_inc_ref(x_6);
x_560 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_560, 0, x_525);
lean_closure_set(x_560, 1, x_6);
lean_closure_set(x_560, 2, x_8);
lean_closure_set(x_560, 3, x_557);
lean_closure_set(x_560, 4, x_558);
lean_closure_set(x_560, 5, x_7);
lean_closure_set(x_560, 6, x_11);
lean_closure_set(x_560, 7, x_16);
lean_closure_set(x_560, 8, x_3);
lean_closure_set(x_560, 9, x_556);
lean_closure_set(x_560, 10, x_12);
lean_closure_set(x_560, 11, x_13);
lean_closure_set(x_560, 12, x_14);
lean_closure_set(x_560, 13, x_15);
lean_closure_set(x_560, 14, x_555);
lean_closure_set(x_560, 15, x_559);
lean_closure_set(x_560, 16, x_2);
lean_closure_set(x_560, 17, x_499);
lean_closure_set(x_560, 18, x_498);
x_561 = lean_nat_add(x_536, x_499);
lean_dec(x_536);
if (lean_is_scalar(x_547)) {
 x_562 = lean_alloc_ctor(0, 3, 0);
} else {
 x_562 = x_547;
}
lean_ctor_set(x_562, 0, x_535);
lean_ctor_set(x_562, 1, x_561);
lean_ctor_set(x_562, 2, x_537);
lean_inc(x_3);
x_563 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_563, 0, x_478);
lean_closure_set(x_563, 1, x_501);
lean_closure_set(x_563, 2, x_514);
lean_closure_set(x_563, 3, x_527);
lean_closure_set(x_563, 4, x_540);
lean_closure_set(x_563, 5, x_562);
lean_closure_set(x_563, 6, x_2);
lean_closure_set(x_563, 7, x_3);
x_564 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_512, x_538, x_560);
lean_inc(x_3);
x_565 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_564, x_563);
x_484 = x_565;
goto block_487;
}
}
}
}
}
}
block_487:
{
lean_object* x_485; lean_object* x_486; 
lean_inc(x_3);
x_485 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_484, x_4);
x_486 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_485, x_483);
return x_486;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_581; 
x_566 = lean_ctor_get(x_22, 0);
lean_inc(x_566);
lean_dec(x_22);
x_567 = lean_ctor_get(x_23, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_568 = x_23;
} else {
 lean_dec_ref(x_23);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_24, 0);
lean_inc(x_569);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_570 = x_24;
} else {
 lean_dec_ref(x_24);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_25, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_572 = x_25;
} else {
 lean_dec_ref(x_25);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_26, 0);
x_574 = lean_ctor_get(x_26, 1);
x_575 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_576 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_576, 0, x_2);
lean_closure_set(x_576, 1, x_16);
lean_closure_set(x_576, 2, x_19);
x_581 = lean_nat_dec_lt(x_574, x_575);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_572)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_572;
}
lean_ctor_set(x_582, 0, x_26);
lean_ctor_set(x_582, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_583 = lean_alloc_ctor(0, 2, 0);
} else {
 x_583 = x_570;
}
lean_ctor_set(x_583, 0, x_569);
lean_ctor_set(x_583, 1, x_582);
if (lean_is_scalar(x_568)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_568;
}
lean_ctor_set(x_584, 0, x_567);
lean_ctor_set(x_584, 1, x_583);
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_566);
lean_ctor_set(x_585, 1, x_584);
lean_ctor_set(x_17, 1, x_585);
x_586 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_586, 0, x_17);
x_587 = lean_apply_2(x_2, lean_box(0), x_586);
x_577 = x_587;
goto block_580;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
lean_inc(x_575);
lean_inc(x_574);
lean_inc_ref(x_573);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_588 = x_26;
} else {
 lean_dec_ref(x_26);
 x_588 = lean_box(0);
}
x_589 = lean_ctor_get(x_569, 0);
x_590 = lean_ctor_get(x_569, 1);
x_591 = lean_ctor_get(x_569, 2);
x_592 = lean_array_fget(x_573, x_574);
x_593 = lean_unsigned_to_nat(1u);
x_594 = lean_nat_add(x_574, x_593);
lean_dec(x_574);
if (lean_is_scalar(x_588)) {
 x_595 = lean_alloc_ctor(0, 3, 0);
} else {
 x_595 = x_588;
}
lean_ctor_set(x_595, 0, x_573);
lean_ctor_set(x_595, 1, x_594);
lean_ctor_set(x_595, 2, x_575);
x_596 = lean_nat_dec_lt(x_590, x_591);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_592);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_572)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_572;
}
lean_ctor_set(x_597, 0, x_595);
lean_ctor_set(x_597, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_570;
}
lean_ctor_set(x_598, 0, x_569);
lean_ctor_set(x_598, 1, x_597);
if (lean_is_scalar(x_568)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_568;
}
lean_ctor_set(x_599, 0, x_567);
lean_ctor_set(x_599, 1, x_598);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_566);
lean_ctor_set(x_600, 1, x_599);
lean_ctor_set(x_17, 1, x_600);
x_601 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_601, 0, x_17);
x_602 = lean_apply_2(x_2, lean_box(0), x_601);
x_577 = x_602;
goto block_580;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
lean_inc(x_591);
lean_inc(x_590);
lean_inc_ref(x_589);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 x_603 = x_569;
} else {
 lean_dec_ref(x_569);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_567, 0);
x_605 = lean_ctor_get(x_567, 1);
x_606 = lean_ctor_get(x_567, 2);
x_607 = lean_array_fget(x_589, x_590);
x_608 = lean_nat_add(x_590, x_593);
lean_dec(x_590);
if (lean_is_scalar(x_603)) {
 x_609 = lean_alloc_ctor(0, 3, 0);
} else {
 x_609 = x_603;
}
lean_ctor_set(x_609, 0, x_589);
lean_ctor_set(x_609, 1, x_608);
lean_ctor_set(x_609, 2, x_591);
x_610 = lean_nat_dec_lt(x_605, x_606);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_607);
lean_dec(x_592);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_572)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_572;
}
lean_ctor_set(x_611, 0, x_595);
lean_ctor_set(x_611, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_570;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_611);
if (lean_is_scalar(x_568)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_568;
}
lean_ctor_set(x_613, 0, x_567);
lean_ctor_set(x_613, 1, x_612);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_566);
lean_ctor_set(x_614, 1, x_613);
lean_ctor_set(x_17, 1, x_614);
x_615 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_615, 0, x_17);
x_616 = lean_apply_2(x_2, lean_box(0), x_615);
x_577 = x_616;
goto block_580;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
lean_inc(x_606);
lean_inc(x_605);
lean_inc_ref(x_604);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 x_617 = x_567;
} else {
 lean_dec_ref(x_567);
 x_617 = lean_box(0);
}
x_618 = lean_ctor_get(x_566, 0);
x_619 = lean_ctor_get(x_566, 1);
x_620 = lean_ctor_get(x_566, 2);
x_621 = lean_array_fget(x_604, x_605);
x_622 = lean_nat_add(x_605, x_593);
lean_dec(x_605);
if (lean_is_scalar(x_617)) {
 x_623 = lean_alloc_ctor(0, 3, 0);
} else {
 x_623 = x_617;
}
lean_ctor_set(x_623, 0, x_604);
lean_ctor_set(x_623, 1, x_622);
lean_ctor_set(x_623, 2, x_606);
x_624 = lean_nat_dec_lt(x_619, x_620);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_621);
lean_dec(x_607);
lean_dec(x_592);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_572)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_572;
}
lean_ctor_set(x_625, 0, x_595);
lean_ctor_set(x_625, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_570;
}
lean_ctor_set(x_626, 0, x_609);
lean_ctor_set(x_626, 1, x_625);
if (lean_is_scalar(x_568)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_568;
}
lean_ctor_set(x_627, 0, x_623);
lean_ctor_set(x_627, 1, x_626);
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_566);
lean_ctor_set(x_628, 1, x_627);
lean_ctor_set(x_17, 1, x_628);
x_629 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_629, 0, x_17);
x_630 = lean_apply_2(x_2, lean_box(0), x_629);
x_577 = x_630;
goto block_580;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; 
lean_inc(x_620);
lean_inc(x_619);
lean_inc_ref(x_618);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 x_631 = x_566;
} else {
 lean_dec_ref(x_566);
 x_631 = lean_box(0);
}
x_632 = lean_ctor_get(x_28, 0);
x_633 = lean_ctor_get(x_28, 1);
x_634 = lean_ctor_get(x_28, 2);
x_635 = lean_array_fget(x_618, x_619);
x_636 = lean_nat_add(x_619, x_593);
lean_dec(x_619);
if (lean_is_scalar(x_631)) {
 x_637 = lean_alloc_ctor(0, 3, 0);
} else {
 x_637 = x_631;
}
lean_ctor_set(x_637, 0, x_618);
lean_ctor_set(x_637, 1, x_636);
lean_ctor_set(x_637, 2, x_620);
x_638 = lean_nat_dec_lt(x_633, x_634);
if (x_638 == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_635);
lean_dec(x_621);
lean_dec(x_607);
lean_dec(x_592);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_572)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_572;
}
lean_ctor_set(x_639, 0, x_595);
lean_ctor_set(x_639, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_570;
}
lean_ctor_set(x_640, 0, x_609);
lean_ctor_set(x_640, 1, x_639);
if (lean_is_scalar(x_568)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_568;
}
lean_ctor_set(x_641, 0, x_623);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_637);
lean_ctor_set(x_642, 1, x_641);
lean_ctor_set(x_17, 1, x_642);
x_643 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_643, 0, x_17);
x_644 = lean_apply_2(x_2, lean_box(0), x_643);
x_577 = x_644;
goto block_580;
}
else
{
lean_object* x_645; lean_object* x_646; uint8_t x_647; uint8_t x_648; 
lean_inc(x_634);
lean_inc(x_633);
lean_inc_ref(x_632);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_568);
lean_free_object(x_17);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_645 = x_28;
} else {
 lean_dec_ref(x_28);
 x_645 = lean_box(0);
}
x_646 = lean_ctor_get(x_635, 1);
x_647 = lean_ctor_get_uint8(x_635, sizeof(void*)*2);
x_648 = lean_nat_dec_eq(x_646, x_5);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_645);
lean_dec_ref(x_637);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec_ref(x_623);
lean_dec(x_621);
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec_ref(x_595);
lean_dec(x_592);
lean_dec(x_571);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_649 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_650 = l_instInhabitedOfMonad___redArg(x_6, x_649);
x_651 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_652 = l_panic___redArg(x_650, x_651);
x_577 = x_652;
goto block_580;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_621);
x_653 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_653, 0, x_621);
lean_closure_set(x_653, 1, x_2);
lean_closure_set(x_653, 2, x_7);
x_654 = lean_array_fget_borrowed(x_632, x_633);
x_655 = lean_box(x_9);
x_656 = lean_box(x_10);
x_657 = lean_box(x_647);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_654);
lean_inc(x_3);
lean_inc_ref(x_6);
x_658 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_658, 0, x_621);
lean_closure_set(x_658, 1, x_6);
lean_closure_set(x_658, 2, x_8);
lean_closure_set(x_658, 3, x_655);
lean_closure_set(x_658, 4, x_656);
lean_closure_set(x_658, 5, x_7);
lean_closure_set(x_658, 6, x_11);
lean_closure_set(x_658, 7, x_16);
lean_closure_set(x_658, 8, x_3);
lean_closure_set(x_658, 9, x_654);
lean_closure_set(x_658, 10, x_12);
lean_closure_set(x_658, 11, x_13);
lean_closure_set(x_658, 12, x_14);
lean_closure_set(x_658, 13, x_15);
lean_closure_set(x_658, 14, x_653);
lean_closure_set(x_658, 15, x_657);
lean_closure_set(x_658, 16, x_2);
lean_closure_set(x_658, 17, x_593);
lean_closure_set(x_658, 18, x_592);
x_659 = lean_nat_add(x_633, x_593);
lean_dec(x_633);
if (lean_is_scalar(x_645)) {
 x_660 = lean_alloc_ctor(0, 3, 0);
} else {
 x_660 = x_645;
}
lean_ctor_set(x_660, 0, x_632);
lean_ctor_set(x_660, 1, x_659);
lean_ctor_set(x_660, 2, x_634);
lean_inc(x_3);
x_661 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_661, 0, x_571);
lean_closure_set(x_661, 1, x_595);
lean_closure_set(x_661, 2, x_609);
lean_closure_set(x_661, 3, x_623);
lean_closure_set(x_661, 4, x_637);
lean_closure_set(x_661, 5, x_660);
lean_closure_set(x_661, 6, x_2);
lean_closure_set(x_661, 7, x_3);
x_662 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_607, x_635, x_658);
lean_inc(x_3);
x_663 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_662, x_661);
x_577 = x_663;
goto block_580;
}
}
}
}
}
}
block_580:
{
lean_object* x_578; lean_object* x_579; 
lean_inc(x_3);
x_578 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_577, x_4);
x_579 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_578, x_576);
return x_579;
}
}
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_681; 
x_664 = lean_ctor_get(x_17, 0);
lean_inc(x_664);
lean_dec(x_17);
x_665 = lean_ctor_get(x_22, 0);
lean_inc(x_665);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_666 = x_22;
} else {
 lean_dec_ref(x_22);
 x_666 = lean_box(0);
}
x_667 = lean_ctor_get(x_23, 0);
lean_inc(x_667);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_668 = x_23;
} else {
 lean_dec_ref(x_23);
 x_668 = lean_box(0);
}
x_669 = lean_ctor_get(x_24, 0);
lean_inc(x_669);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_670 = x_24;
} else {
 lean_dec_ref(x_24);
 x_670 = lean_box(0);
}
x_671 = lean_ctor_get(x_25, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_672 = x_25;
} else {
 lean_dec_ref(x_25);
 x_672 = lean_box(0);
}
x_673 = lean_ctor_get(x_26, 0);
x_674 = lean_ctor_get(x_26, 1);
x_675 = lean_ctor_get(x_26, 2);
lean_inc(x_16);
lean_inc(x_2);
x_676 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 4, 3);
lean_closure_set(x_676, 0, x_2);
lean_closure_set(x_676, 1, x_16);
lean_closure_set(x_676, 2, x_19);
x_681 = lean_nat_dec_lt(x_674, x_675);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_672)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_672;
}
lean_ctor_set(x_682, 0, x_26);
lean_ctor_set(x_682, 1, x_671);
if (lean_is_scalar(x_670)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_670;
}
lean_ctor_set(x_683, 0, x_669);
lean_ctor_set(x_683, 1, x_682);
if (lean_is_scalar(x_668)) {
 x_684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_684 = x_668;
}
lean_ctor_set(x_684, 0, x_667);
lean_ctor_set(x_684, 1, x_683);
if (lean_is_scalar(x_666)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_666;
}
lean_ctor_set(x_685, 0, x_665);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_686, 0, x_664);
lean_ctor_set(x_686, 1, x_685);
x_687 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_687, 0, x_686);
x_688 = lean_apply_2(x_2, lean_box(0), x_687);
x_677 = x_688;
goto block_680;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; 
lean_inc(x_675);
lean_inc(x_674);
lean_inc_ref(x_673);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_689 = x_26;
} else {
 lean_dec_ref(x_26);
 x_689 = lean_box(0);
}
x_690 = lean_ctor_get(x_669, 0);
x_691 = lean_ctor_get(x_669, 1);
x_692 = lean_ctor_get(x_669, 2);
x_693 = lean_array_fget(x_673, x_674);
x_694 = lean_unsigned_to_nat(1u);
x_695 = lean_nat_add(x_674, x_694);
lean_dec(x_674);
if (lean_is_scalar(x_689)) {
 x_696 = lean_alloc_ctor(0, 3, 0);
} else {
 x_696 = x_689;
}
lean_ctor_set(x_696, 0, x_673);
lean_ctor_set(x_696, 1, x_695);
lean_ctor_set(x_696, 2, x_675);
x_697 = lean_nat_dec_lt(x_691, x_692);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_693);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_672)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_672;
}
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_671);
if (lean_is_scalar(x_670)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_670;
}
lean_ctor_set(x_699, 0, x_669);
lean_ctor_set(x_699, 1, x_698);
if (lean_is_scalar(x_668)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_668;
}
lean_ctor_set(x_700, 0, x_667);
lean_ctor_set(x_700, 1, x_699);
if (lean_is_scalar(x_666)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_666;
}
lean_ctor_set(x_701, 0, x_665);
lean_ctor_set(x_701, 1, x_700);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_664);
lean_ctor_set(x_702, 1, x_701);
x_703 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_703, 0, x_702);
x_704 = lean_apply_2(x_2, lean_box(0), x_703);
x_677 = x_704;
goto block_680;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; 
lean_inc(x_692);
lean_inc(x_691);
lean_inc_ref(x_690);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 lean_ctor_release(x_669, 2);
 x_705 = x_669;
} else {
 lean_dec_ref(x_669);
 x_705 = lean_box(0);
}
x_706 = lean_ctor_get(x_667, 0);
x_707 = lean_ctor_get(x_667, 1);
x_708 = lean_ctor_get(x_667, 2);
x_709 = lean_array_fget(x_690, x_691);
x_710 = lean_nat_add(x_691, x_694);
lean_dec(x_691);
if (lean_is_scalar(x_705)) {
 x_711 = lean_alloc_ctor(0, 3, 0);
} else {
 x_711 = x_705;
}
lean_ctor_set(x_711, 0, x_690);
lean_ctor_set(x_711, 1, x_710);
lean_ctor_set(x_711, 2, x_692);
x_712 = lean_nat_dec_lt(x_707, x_708);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_709);
lean_dec(x_693);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_672)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_672;
}
lean_ctor_set(x_713, 0, x_696);
lean_ctor_set(x_713, 1, x_671);
if (lean_is_scalar(x_670)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_670;
}
lean_ctor_set(x_714, 0, x_711);
lean_ctor_set(x_714, 1, x_713);
if (lean_is_scalar(x_668)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_668;
}
lean_ctor_set(x_715, 0, x_667);
lean_ctor_set(x_715, 1, x_714);
if (lean_is_scalar(x_666)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_666;
}
lean_ctor_set(x_716, 0, x_665);
lean_ctor_set(x_716, 1, x_715);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_664);
lean_ctor_set(x_717, 1, x_716);
x_718 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_718, 0, x_717);
x_719 = lean_apply_2(x_2, lean_box(0), x_718);
x_677 = x_719;
goto block_680;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
lean_inc(x_708);
lean_inc(x_707);
lean_inc_ref(x_706);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 lean_ctor_release(x_667, 2);
 x_720 = x_667;
} else {
 lean_dec_ref(x_667);
 x_720 = lean_box(0);
}
x_721 = lean_ctor_get(x_665, 0);
x_722 = lean_ctor_get(x_665, 1);
x_723 = lean_ctor_get(x_665, 2);
x_724 = lean_array_fget(x_706, x_707);
x_725 = lean_nat_add(x_707, x_694);
lean_dec(x_707);
if (lean_is_scalar(x_720)) {
 x_726 = lean_alloc_ctor(0, 3, 0);
} else {
 x_726 = x_720;
}
lean_ctor_set(x_726, 0, x_706);
lean_ctor_set(x_726, 1, x_725);
lean_ctor_set(x_726, 2, x_708);
x_727 = lean_nat_dec_lt(x_722, x_723);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_724);
lean_dec(x_709);
lean_dec(x_693);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_672)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_672;
}
lean_ctor_set(x_728, 0, x_696);
lean_ctor_set(x_728, 1, x_671);
if (lean_is_scalar(x_670)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_670;
}
lean_ctor_set(x_729, 0, x_711);
lean_ctor_set(x_729, 1, x_728);
if (lean_is_scalar(x_668)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_668;
}
lean_ctor_set(x_730, 0, x_726);
lean_ctor_set(x_730, 1, x_729);
if (lean_is_scalar(x_666)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_666;
}
lean_ctor_set(x_731, 0, x_665);
lean_ctor_set(x_731, 1, x_730);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_664);
lean_ctor_set(x_732, 1, x_731);
x_733 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_733, 0, x_732);
x_734 = lean_apply_2(x_2, lean_box(0), x_733);
x_677 = x_734;
goto block_680;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; 
lean_inc(x_723);
lean_inc(x_722);
lean_inc_ref(x_721);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 lean_ctor_release(x_665, 2);
 x_735 = x_665;
} else {
 lean_dec_ref(x_665);
 x_735 = lean_box(0);
}
x_736 = lean_ctor_get(x_664, 0);
x_737 = lean_ctor_get(x_664, 1);
x_738 = lean_ctor_get(x_664, 2);
x_739 = lean_array_fget(x_721, x_722);
x_740 = lean_nat_add(x_722, x_694);
lean_dec(x_722);
if (lean_is_scalar(x_735)) {
 x_741 = lean_alloc_ctor(0, 3, 0);
} else {
 x_741 = x_735;
}
lean_ctor_set(x_741, 0, x_721);
lean_ctor_set(x_741, 1, x_740);
lean_ctor_set(x_741, 2, x_723);
x_742 = lean_nat_dec_lt(x_737, x_738);
if (x_742 == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_709);
lean_dec(x_693);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_672)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_672;
}
lean_ctor_set(x_743, 0, x_696);
lean_ctor_set(x_743, 1, x_671);
if (lean_is_scalar(x_670)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_670;
}
lean_ctor_set(x_744, 0, x_711);
lean_ctor_set(x_744, 1, x_743);
if (lean_is_scalar(x_668)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_668;
}
lean_ctor_set(x_745, 0, x_726);
lean_ctor_set(x_745, 1, x_744);
if (lean_is_scalar(x_666)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_666;
}
lean_ctor_set(x_746, 0, x_741);
lean_ctor_set(x_746, 1, x_745);
x_747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_747, 0, x_664);
lean_ctor_set(x_747, 1, x_746);
x_748 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_748, 0, x_747);
x_749 = lean_apply_2(x_2, lean_box(0), x_748);
x_677 = x_749;
goto block_680;
}
else
{
lean_object* x_750; lean_object* x_751; uint8_t x_752; uint8_t x_753; 
lean_inc(x_738);
lean_inc(x_737);
lean_inc_ref(x_736);
lean_dec(x_672);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_666);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 lean_ctor_release(x_664, 2);
 x_750 = x_664;
} else {
 lean_dec_ref(x_664);
 x_750 = lean_box(0);
}
x_751 = lean_ctor_get(x_739, 1);
x_752 = lean_ctor_get_uint8(x_739, sizeof(void*)*2);
x_753 = lean_nat_dec_eq(x_751, x_5);
if (x_753 == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_750);
lean_dec_ref(x_741);
lean_dec(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_726);
lean_dec(x_724);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_696);
lean_dec(x_693);
lean_dec(x_671);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_754 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_755 = l_instInhabitedOfMonad___redArg(x_6, x_754);
x_756 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_757 = l_panic___redArg(x_755, x_756);
x_677 = x_757;
goto block_680;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_724);
x_758 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 4, 3);
lean_closure_set(x_758, 0, x_724);
lean_closure_set(x_758, 1, x_2);
lean_closure_set(x_758, 2, x_7);
x_759 = lean_array_fget_borrowed(x_736, x_737);
x_760 = lean_box(x_9);
x_761 = lean_box(x_10);
x_762 = lean_box(x_752);
lean_inc(x_2);
lean_inc_ref(x_14);
lean_inc(x_759);
lean_inc(x_3);
lean_inc_ref(x_6);
x_763 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 19);
lean_closure_set(x_763, 0, x_724);
lean_closure_set(x_763, 1, x_6);
lean_closure_set(x_763, 2, x_8);
lean_closure_set(x_763, 3, x_760);
lean_closure_set(x_763, 4, x_761);
lean_closure_set(x_763, 5, x_7);
lean_closure_set(x_763, 6, x_11);
lean_closure_set(x_763, 7, x_16);
lean_closure_set(x_763, 8, x_3);
lean_closure_set(x_763, 9, x_759);
lean_closure_set(x_763, 10, x_12);
lean_closure_set(x_763, 11, x_13);
lean_closure_set(x_763, 12, x_14);
lean_closure_set(x_763, 13, x_15);
lean_closure_set(x_763, 14, x_758);
lean_closure_set(x_763, 15, x_762);
lean_closure_set(x_763, 16, x_2);
lean_closure_set(x_763, 17, x_694);
lean_closure_set(x_763, 18, x_693);
x_764 = lean_nat_add(x_737, x_694);
lean_dec(x_737);
if (lean_is_scalar(x_750)) {
 x_765 = lean_alloc_ctor(0, 3, 0);
} else {
 x_765 = x_750;
}
lean_ctor_set(x_765, 0, x_736);
lean_ctor_set(x_765, 1, x_764);
lean_ctor_set(x_765, 2, x_738);
lean_inc(x_3);
x_766 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51), 9, 8);
lean_closure_set(x_766, 0, x_671);
lean_closure_set(x_766, 1, x_696);
lean_closure_set(x_766, 2, x_711);
lean_closure_set(x_766, 3, x_726);
lean_closure_set(x_766, 4, x_741);
lean_closure_set(x_766, 5, x_765);
lean_closure_set(x_766, 6, x_2);
lean_closure_set(x_766, 7, x_3);
x_767 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_6, x_14, x_709, x_739, x_763);
lean_inc(x_3);
x_768 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_767, x_766);
x_677 = x_768;
goto block_680;
}
}
}
}
}
}
block_680:
{
lean_object* x_678; lean_object* x_679; 
lean_inc(x_3);
x_678 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_677, x_4);
x_679 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_678, x_676);
return x_679;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_9);
x_21 = lean_unbox(x_10);
x_22 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_5);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Array_append___redArg(x_1, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_5);
lean_ctor_set(x_17, 4, x_6);
lean_ctor_set(x_17, 5, x_7);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 4, x_11);
lean_ctor_set(x_18, 5, x_12);
lean_ctor_set(x_18, 6, x_13);
lean_ctor_set(x_18, 7, x_16);
x_19 = lean_apply_2(x_14, lean_box(0), x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 15, 14);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_8);
lean_closure_set(x_23, 8, x_9);
lean_closure_set(x_23, 9, x_10);
lean_closure_set(x_23, 10, x_11);
lean_closure_set(x_23, 11, x_12);
lean_closure_set(x_23, 12, x_22);
lean_closure_set(x_23, 13, x_13);
x_24 = lean_apply_1(x_14, x_15);
x_25 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_24, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
lean_inc(x_17);
lean_inc_ref(x_5);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 17, 16);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
lean_closure_set(x_26, 4, x_6);
lean_closure_set(x_26, 5, x_7);
lean_closure_set(x_26, 6, x_8);
lean_closure_set(x_26, 7, x_9);
lean_closure_set(x_26, 8, x_10);
lean_closure_set(x_26, 9, x_11);
lean_closure_set(x_26, 10, x_12);
lean_closure_set(x_26, 11, x_13);
lean_closure_set(x_26, 12, x_14);
lean_closure_set(x_26, 13, x_15);
lean_closure_set(x_26, 14, x_16);
lean_closure_set(x_26, 15, x_17);
x_27 = lean_array_get_size(x_5);
x_28 = lean_array_get_size(x_25);
x_29 = lean_array_get_size(x_18);
x_30 = lean_array_get_size(x_24);
lean_inc(x_20);
x_31 = l_Array_toSubarray___redArg(x_19, x_20, x_21);
lean_inc(x_20);
x_32 = l_Array_toSubarray___redArg(x_5, x_20, x_27);
lean_inc(x_20);
x_33 = l_Array_toSubarray___redArg(x_25, x_20, x_28);
lean_inc(x_20);
x_34 = l_Array_toSubarray___redArg(x_18, x_20, x_29);
lean_inc(x_20);
x_35 = l_Array_toSubarray___redArg(x_24, x_20, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_WellFounded_opaqueFix_u2083___redArg(x_23, x_20, x_40, lean_box(0));
x_42 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_41, x_26);
return x_42;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_27);
lean_inc(x_28);
x_30 = l_Lean_mkConst(x_28, x_1);
x_31 = l_Lean_mkAppN(x_30, x_2);
lean_inc_ref(x_3);
x_32 = l_Lean_Expr_app___override(x_31, x_3);
x_33 = l_Lean_mkAppN(x_32, x_4);
lean_inc_ref(x_33);
x_34 = l_Lean_indentExpr(x_33);
lean_inc(x_20);
lean_inc(x_16);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 24, 23);
lean_closure_set(x_35, 0, x_29);
lean_closure_set(x_35, 1, x_5);
lean_closure_set(x_35, 2, x_6);
lean_closure_set(x_35, 3, x_7);
lean_closure_set(x_35, 4, x_8);
lean_closure_set(x_35, 5, x_9);
lean_closure_set(x_35, 6, x_10);
lean_closure_set(x_35, 7, x_11);
lean_closure_set(x_35, 8, x_28);
lean_closure_set(x_35, 9, x_12);
lean_closure_set(x_35, 10, x_2);
lean_closure_set(x_35, 11, x_3);
lean_closure_set(x_35, 12, x_4);
lean_closure_set(x_35, 13, x_13);
lean_closure_set(x_35, 14, x_14);
lean_closure_set(x_35, 15, x_15);
lean_closure_set(x_35, 16, x_16);
lean_closure_set(x_35, 17, x_17);
lean_closure_set(x_35, 18, x_18);
lean_closure_set(x_35, 19, x_19);
lean_closure_set(x_35, 20, x_20);
lean_closure_set(x_35, 21, x_21);
lean_closure_set(x_35, 22, x_22);
lean_inc(x_16);
lean_inc(x_23);
lean_inc_ref(x_33);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 6, 5);
lean_closure_set(x_36, 0, x_20);
lean_closure_set(x_36, 1, x_33);
lean_closure_set(x_36, 2, x_23);
lean_closure_set(x_36, 3, x_16);
lean_closure_set(x_36, 4, x_35);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_apply_2(x_23, lean_box(0), x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_40);
x_44 = lean_apply_2(x_25, lean_box(0), x_43);
x_45 = lean_apply_1(x_26, lean_box(0));
lean_inc(x_16);
x_46 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_44, x_45);
x_47 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_46, x_36);
return x_47;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
_start:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_22);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 27, 26);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_4);
lean_closure_set(x_28, 4, x_5);
lean_closure_set(x_28, 5, x_6);
lean_closure_set(x_28, 6, x_7);
lean_closure_set(x_28, 7, x_8);
lean_closure_set(x_28, 8, x_9);
lean_closure_set(x_28, 9, x_10);
lean_closure_set(x_28, 10, x_11);
lean_closure_set(x_28, 11, x_12);
lean_closure_set(x_28, 12, x_13);
lean_closure_set(x_28, 13, x_14);
lean_closure_set(x_28, 14, x_15);
lean_closure_set(x_28, 15, x_16);
lean_closure_set(x_28, 16, x_27);
lean_closure_set(x_28, 17, x_17);
lean_closure_set(x_28, 18, x_18);
lean_closure_set(x_28, 19, x_19);
lean_closure_set(x_28, 20, x_20);
lean_closure_set(x_28, 21, x_21);
lean_closure_set(x_28, 22, x_22);
lean_closure_set(x_28, 23, x_23);
lean_closure_set(x_28, 24, x_24);
lean_closure_set(x_28, 25, x_25);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(x_29, 0, x_26);
x_30 = lean_apply_2(x_22, lean_box(0), x_29);
x_31 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_30, x_28);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
_start:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36) {
_start:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_array_get_size(x_1);
x_38 = lean_box(x_9);
x_39 = lean_box(x_10);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 19, 15);
lean_closure_set(x_40, 0, x_37);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_4);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_6);
lean_closure_set(x_40, 6, x_7);
lean_closure_set(x_40, 7, x_8);
lean_closure_set(x_40, 8, x_38);
lean_closure_set(x_40, 9, x_39);
lean_closure_set(x_40, 10, x_11);
lean_closure_set(x_40, 11, x_12);
lean_closure_set(x_40, 12, x_13);
lean_closure_set(x_40, 13, x_14);
lean_closure_set(x_40, 14, x_15);
lean_inc(x_7);
lean_inc(x_3);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 27, 26);
lean_closure_set(x_41, 0, x_16);
lean_closure_set(x_41, 1, x_17);
lean_closure_set(x_41, 2, x_18);
lean_closure_set(x_41, 3, x_19);
lean_closure_set(x_41, 4, x_20);
lean_closure_set(x_41, 5, x_21);
lean_closure_set(x_41, 6, x_22);
lean_closure_set(x_41, 7, x_23);
lean_closure_set(x_41, 8, x_24);
lean_closure_set(x_41, 9, x_25);
lean_closure_set(x_41, 10, x_26);
lean_closure_set(x_41, 11, x_27);
lean_closure_set(x_41, 12, x_2);
lean_closure_set(x_41, 13, x_28);
lean_closure_set(x_41, 14, x_29);
lean_closure_set(x_41, 15, x_3);
lean_closure_set(x_41, 16, x_1);
lean_closure_set(x_41, 17, x_5);
lean_closure_set(x_41, 18, x_37);
lean_closure_set(x_41, 19, x_30);
lean_closure_set(x_41, 20, x_40);
lean_closure_set(x_41, 21, x_7);
lean_closure_set(x_41, 22, x_31);
lean_closure_set(x_41, 23, x_32);
lean_closure_set(x_41, 24, x_33);
lean_closure_set(x_41, 25, x_34);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(x_42, 0, x_37);
lean_closure_set(x_42, 1, x_35);
x_43 = lean_apply_2(x_7, lean_box(0), x_42);
x_44 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_43, x_41);
return x_44;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
lean_object* x_34 = _args[33];
lean_object* x_35 = _args[34];
lean_object* x_36 = _args[35];
_start:
{
uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_unbox(x_9);
x_38 = lean_unbox(x_10);
x_39 = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37, x_38, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
return x_39;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, uint8_t x_27, uint8_t x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed), 17, 16);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_1);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_3);
lean_closure_set(x_40, 4, x_4);
lean_closure_set(x_40, 5, x_5);
lean_closure_set(x_40, 6, x_6);
lean_closure_set(x_40, 7, x_7);
lean_closure_set(x_40, 8, x_8);
lean_closure_set(x_40, 9, x_9);
lean_closure_set(x_40, 10, x_10);
lean_closure_set(x_40, 11, x_11);
lean_closure_set(x_40, 12, x_12);
lean_closure_set(x_40, 13, x_13);
lean_closure_set(x_40, 14, x_14);
lean_closure_set(x_40, 15, x_15);
if (x_27 == 0)
{
lean_dec(x_38);
lean_free_object(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_63;
}
else
{
if (x_28 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_18);
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_16, 1);
lean_inc(x_65);
lean_inc_ref(x_8);
x_66 = lean_array_to_list(x_8);
lean_inc(x_66);
lean_inc(x_7);
x_67 = l_Lean_mkConst(x_7, x_66);
x_68 = l_Lean_mkAppN(x_67, x_9);
lean_inc_ref(x_10);
x_69 = l_Lean_Expr_app___override(x_68, x_10);
x_70 = l_Lean_mkAppN(x_69, x_11);
lean_inc_ref(x_70);
x_71 = l_Lean_indentExpr(x_70);
x_72 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_71);
lean_ctor_set(x_33, 0, x_72);
x_73 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_74 = lean_box(x_19);
x_75 = lean_box(x_27);
lean_inc_ref(x_70);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_20);
lean_inc(x_15);
x_76 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 36, 35);
lean_closure_set(x_76, 0, x_17);
lean_closure_set(x_76, 1, x_12);
lean_closure_set(x_76, 2, x_15);
lean_closure_set(x_76, 3, x_29);
lean_closure_set(x_76, 4, x_25);
lean_closure_set(x_76, 5, x_22);
lean_closure_set(x_76, 6, x_20);
lean_closure_set(x_76, 7, x_30);
lean_closure_set(x_76, 8, x_74);
lean_closure_set(x_76, 9, x_75);
lean_closure_set(x_76, 10, x_21);
lean_closure_set(x_76, 11, x_31);
lean_closure_set(x_76, 12, x_37);
lean_closure_set(x_76, 13, x_16);
lean_closure_set(x_76, 14, x_32);
lean_closure_set(x_76, 15, x_66);
lean_closure_set(x_76, 16, x_9);
lean_closure_set(x_76, 17, x_10);
lean_closure_set(x_76, 18, x_11);
lean_closure_set(x_76, 19, x_38);
lean_closure_set(x_76, 20, x_1);
lean_closure_set(x_76, 21, x_2);
lean_closure_set(x_76, 22, x_3);
lean_closure_set(x_76, 23, x_4);
lean_closure_set(x_76, 24, x_5);
lean_closure_set(x_76, 25, x_6);
lean_closure_set(x_76, 26, x_8);
lean_closure_set(x_76, 27, x_13);
lean_closure_set(x_76, 28, x_14);
lean_closure_set(x_76, 29, x_26);
lean_closure_set(x_76, 30, x_73);
lean_closure_set(x_76, 31, x_64);
lean_closure_set(x_76, 32, x_65);
lean_closure_set(x_76, 33, x_7);
lean_closure_set(x_76, 34, x_70);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_33);
lean_ctor_set(x_77, 1, x_73);
x_78 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_78, 0, x_77);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_79, 0, x_70);
x_80 = lean_apply_2(x_20, lean_box(0), x_79);
x_81 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 2);
lean_closure_set(x_81, 0, x_80);
lean_closure_set(x_81, 1, x_78);
x_82 = lean_apply_2(x_64, lean_box(0), x_81);
x_83 = lean_apply_1(x_65, lean_box(0));
lean_inc(x_15);
x_84 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_82, x_83);
x_85 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_84, x_76);
return x_85;
}
else
{
lean_dec(x_38);
lean_free_object(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_63;
}
}
block_63:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
x_43 = lean_array_to_list(x_8);
x_44 = l_Lean_mkConst(x_7, x_43);
x_45 = l_Lean_mkAppN(x_44, x_9);
lean_dec_ref(x_9);
x_46 = l_Lean_Expr_app___override(x_45, x_10);
x_47 = l_Lean_mkAppN(x_46, x_11);
lean_dec_ref(x_11);
lean_inc_ref(x_47);
x_48 = l_Lean_indentExpr(x_47);
x_49 = 1;
x_50 = lean_box(x_19);
x_51 = lean_box(x_49);
lean_inc_ref(x_47);
lean_inc(x_20);
lean_inc(x_15);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 18, 17);
lean_closure_set(x_52, 0, x_17);
lean_closure_set(x_52, 1, x_12);
lean_closure_set(x_52, 2, x_15);
lean_closure_set(x_52, 3, x_18);
lean_closure_set(x_52, 4, x_50);
lean_closure_set(x_52, 5, x_51);
lean_closure_set(x_52, 6, x_20);
lean_closure_set(x_52, 7, x_21);
lean_closure_set(x_52, 8, x_16);
lean_closure_set(x_52, 9, x_22);
lean_closure_set(x_52, 10, x_23);
lean_closure_set(x_52, 11, x_37);
lean_closure_set(x_52, 12, x_24);
lean_closure_set(x_52, 13, x_25);
lean_closure_set(x_52, 14, x_26);
lean_closure_set(x_52, 15, x_40);
lean_closure_set(x_52, 16, x_47);
x_53 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
if (lean_is_scalar(x_39)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_39;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_56, 0, x_47);
x_57 = lean_apply_2(x_20, lean_box(0), x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_55);
x_59 = lean_apply_2(x_41, lean_box(0), x_58);
x_60 = lean_apply_1(x_42, lean_box(0));
lean_inc(x_15);
x_61 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_59, x_60);
x_62 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_61, x_52);
return x_62;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_dec(x_33);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_88);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed), 17, 16);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_1);
lean_closure_set(x_90, 2, x_2);
lean_closure_set(x_90, 3, x_3);
lean_closure_set(x_90, 4, x_4);
lean_closure_set(x_90, 5, x_5);
lean_closure_set(x_90, 6, x_6);
lean_closure_set(x_90, 7, x_7);
lean_closure_set(x_90, 8, x_8);
lean_closure_set(x_90, 9, x_9);
lean_closure_set(x_90, 10, x_10);
lean_closure_set(x_90, 11, x_11);
lean_closure_set(x_90, 12, x_12);
lean_closure_set(x_90, 13, x_13);
lean_closure_set(x_90, 14, x_14);
lean_closure_set(x_90, 15, x_15);
if (x_27 == 0)
{
lean_dec(x_88);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_113;
}
else
{
if (x_28 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_18);
x_114 = lean_ctor_get(x_16, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_16, 1);
lean_inc(x_115);
lean_inc_ref(x_8);
x_116 = lean_array_to_list(x_8);
lean_inc(x_116);
lean_inc(x_7);
x_117 = l_Lean_mkConst(x_7, x_116);
x_118 = l_Lean_mkAppN(x_117, x_9);
lean_inc_ref(x_10);
x_119 = l_Lean_Expr_app___override(x_118, x_10);
x_120 = l_Lean_mkAppN(x_119, x_11);
lean_inc_ref(x_120);
x_121 = l_Lean_indentExpr(x_120);
x_122 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_125 = lean_box(x_19);
x_126 = lean_box(x_27);
lean_inc_ref(x_120);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_20);
lean_inc(x_15);
x_127 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 36, 35);
lean_closure_set(x_127, 0, x_17);
lean_closure_set(x_127, 1, x_12);
lean_closure_set(x_127, 2, x_15);
lean_closure_set(x_127, 3, x_29);
lean_closure_set(x_127, 4, x_25);
lean_closure_set(x_127, 5, x_22);
lean_closure_set(x_127, 6, x_20);
lean_closure_set(x_127, 7, x_30);
lean_closure_set(x_127, 8, x_125);
lean_closure_set(x_127, 9, x_126);
lean_closure_set(x_127, 10, x_21);
lean_closure_set(x_127, 11, x_31);
lean_closure_set(x_127, 12, x_87);
lean_closure_set(x_127, 13, x_16);
lean_closure_set(x_127, 14, x_32);
lean_closure_set(x_127, 15, x_116);
lean_closure_set(x_127, 16, x_9);
lean_closure_set(x_127, 17, x_10);
lean_closure_set(x_127, 18, x_11);
lean_closure_set(x_127, 19, x_88);
lean_closure_set(x_127, 20, x_1);
lean_closure_set(x_127, 21, x_2);
lean_closure_set(x_127, 22, x_3);
lean_closure_set(x_127, 23, x_4);
lean_closure_set(x_127, 24, x_5);
lean_closure_set(x_127, 25, x_6);
lean_closure_set(x_127, 26, x_8);
lean_closure_set(x_127, 27, x_13);
lean_closure_set(x_127, 28, x_14);
lean_closure_set(x_127, 29, x_26);
lean_closure_set(x_127, 30, x_124);
lean_closure_set(x_127, 31, x_114);
lean_closure_set(x_127, 32, x_115);
lean_closure_set(x_127, 33, x_7);
lean_closure_set(x_127, 34, x_120);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_124);
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_129, 0, x_128);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_130, 0, x_120);
x_131 = lean_apply_2(x_20, lean_box(0), x_130);
x_132 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 2);
lean_closure_set(x_132, 0, x_131);
lean_closure_set(x_132, 1, x_129);
x_133 = lean_apply_2(x_114, lean_box(0), x_132);
x_134 = lean_apply_1(x_115, lean_box(0));
lean_inc(x_15);
x_135 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_133, x_134);
x_136 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_135, x_127);
return x_136;
}
else
{
lean_dec(x_88);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_113;
}
}
block_113:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_91 = lean_ctor_get(x_16, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_16, 1);
lean_inc(x_92);
x_93 = lean_array_to_list(x_8);
x_94 = l_Lean_mkConst(x_7, x_93);
x_95 = l_Lean_mkAppN(x_94, x_9);
lean_dec_ref(x_9);
x_96 = l_Lean_Expr_app___override(x_95, x_10);
x_97 = l_Lean_mkAppN(x_96, x_11);
lean_dec_ref(x_11);
lean_inc_ref(x_97);
x_98 = l_Lean_indentExpr(x_97);
x_99 = 1;
x_100 = lean_box(x_19);
x_101 = lean_box(x_99);
lean_inc_ref(x_97);
lean_inc(x_20);
lean_inc(x_15);
x_102 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 18, 17);
lean_closure_set(x_102, 0, x_17);
lean_closure_set(x_102, 1, x_12);
lean_closure_set(x_102, 2, x_15);
lean_closure_set(x_102, 3, x_18);
lean_closure_set(x_102, 4, x_100);
lean_closure_set(x_102, 5, x_101);
lean_closure_set(x_102, 6, x_20);
lean_closure_set(x_102, 7, x_21);
lean_closure_set(x_102, 8, x_16);
lean_closure_set(x_102, 9, x_22);
lean_closure_set(x_102, 10, x_23);
lean_closure_set(x_102, 11, x_87);
lean_closure_set(x_102, 12, x_24);
lean_closure_set(x_102, 13, x_25);
lean_closure_set(x_102, 14, x_26);
lean_closure_set(x_102, 15, x_90);
lean_closure_set(x_102, 16, x_97);
x_103 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
if (lean_is_scalar(x_89)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_89;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
x_105 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_105, 0, x_104);
x_106 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_106, 0, x_97);
x_107 = lean_apply_2(x_20, lean_box(0), x_106);
x_108 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 2);
lean_closure_set(x_108, 0, x_107);
lean_closure_set(x_108, 1, x_105);
x_109 = lean_apply_2(x_91, lean_box(0), x_108);
x_110 = lean_apply_1(x_92, lean_box(0));
lean_inc(x_15);
x_111 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_109, x_110);
x_112 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_111, x_102);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_unbox(x_19);
x_35 = lean_unbox(x_27);
x_36 = lean_unbox(x_28);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_34, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_35, x_36, x_29, x_30, x_31, x_32, x_33);
return x_37;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, uint8_t x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
x_35 = lean_box(x_18);
x_36 = lean_box(x_24);
x_37 = lean_box(x_25);
lean_inc_ref(x_21);
lean_inc(x_14);
lean_inc_ref(x_10);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed), 33, 32);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_3);
lean_closure_set(x_38, 3, x_4);
lean_closure_set(x_38, 4, x_5);
lean_closure_set(x_38, 5, x_6);
lean_closure_set(x_38, 6, x_7);
lean_closure_set(x_38, 7, x_32);
lean_closure_set(x_38, 8, x_8);
lean_closure_set(x_38, 9, x_9);
lean_closure_set(x_38, 10, x_10);
lean_closure_set(x_38, 11, x_11);
lean_closure_set(x_38, 12, x_12);
lean_closure_set(x_38, 13, x_13);
lean_closure_set(x_38, 14, x_14);
lean_closure_set(x_38, 15, x_15);
lean_closure_set(x_38, 16, x_16);
lean_closure_set(x_38, 17, x_17);
lean_closure_set(x_38, 18, x_35);
lean_closure_set(x_38, 19, x_19);
lean_closure_set(x_38, 20, x_20);
lean_closure_set(x_38, 21, x_21);
lean_closure_set(x_38, 22, x_22);
lean_closure_set(x_38, 23, x_23);
lean_closure_set(x_38, 24, x_33);
lean_closure_set(x_38, 25, x_34);
lean_closure_set(x_38, 26, x_36);
lean_closure_set(x_38, 27, x_37);
lean_closure_set(x_38, 28, x_26);
lean_closure_set(x_38, 29, x_27);
lean_closure_set(x_38, 30, x_28);
lean_closure_set(x_38, 31, x_29);
x_39 = l_Array_reverse___redArg(x_30);
x_40 = lean_array_get_size(x_39);
x_41 = l_Array_toSubarray___redArg(x_39, x_33, x_40);
x_42 = l_Array_reverse___redArg(x_10);
x_43 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_size(x_42);
x_46 = 0;
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_21, x_42, x_31, x_45, x_46, x_44);
x_48 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_47, x_38);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_unbox(x_18);
x_34 = lean_unbox(x_24);
x_35 = lean_unbox(x_25);
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_33, x_19, x_20, x_21, x_22, x_23, x_34, x_35, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26) {
_start:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_box(x_12);
x_39 = lean_box(x_18);
x_40 = lean_box(x_19);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_36);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 32, 31);
lean_closure_set(x_41, 0, x_33);
lean_closure_set(x_41, 1, x_34);
lean_closure_set(x_41, 2, x_35);
lean_closure_set(x_41, 3, x_36);
lean_closure_set(x_41, 4, x_32);
lean_closure_set(x_41, 5, x_37);
lean_closure_set(x_41, 6, x_2);
lean_closure_set(x_41, 7, x_3);
lean_closure_set(x_41, 8, x_29);
lean_closure_set(x_41, 9, x_4);
lean_closure_set(x_41, 10, x_5);
lean_closure_set(x_41, 11, x_6);
lean_closure_set(x_41, 12, x_7);
lean_closure_set(x_41, 13, x_8);
lean_closure_set(x_41, 14, x_9);
lean_closure_set(x_41, 15, x_10);
lean_closure_set(x_41, 16, x_11);
lean_closure_set(x_41, 17, x_38);
lean_closure_set(x_41, 18, x_13);
lean_closure_set(x_41, 19, x_14);
lean_closure_set(x_41, 20, x_15);
lean_closure_set(x_41, 21, x_16);
lean_closure_set(x_41, 22, x_17);
lean_closure_set(x_41, 23, x_39);
lean_closure_set(x_41, 24, x_40);
lean_closure_set(x_41, 25, x_20);
lean_closure_set(x_41, 26, x_21);
lean_closure_set(x_41, 27, x_22);
lean_closure_set(x_41, 28, x_23);
lean_closure_set(x_41, 29, x_31);
lean_closure_set(x_41, 30, x_24);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_apply_2(x_5, lean_box(0), x_25);
x_44 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_43, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec_ref(x_36);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(x_46, 0, x_41);
x_47 = lean_array_set(x_25, x_45, x_30);
lean_dec(x_45);
x_48 = lean_apply_2(x_5, lean_box(0), x_47);
x_49 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_48, x_46);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_unbox(x_12);
x_28 = lean_unbox(x_18);
x_29 = lean_unbox(x_19);
x_30 = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27, x_13, x_14, x_15, x_16, x_17, x_28, x_29, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, uint8_t x_20, uint8_t x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_28);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed), 12, 10);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_5);
lean_closure_set(x_29, 6, x_6);
lean_closure_set(x_29, 7, x_7);
lean_closure_set(x_29, 8, x_8);
lean_closure_set(x_29, 9, x_9);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_box(x_20);
x_33 = lean_box(x_21);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
lean_inc(x_3);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 26, 25);
lean_closure_set(x_34, 0, x_4);
lean_closure_set(x_34, 1, x_10);
lean_closure_set(x_34, 2, x_11);
lean_closure_set(x_34, 3, x_28);
lean_closure_set(x_34, 4, x_1);
lean_closure_set(x_34, 5, x_12);
lean_closure_set(x_34, 6, x_13);
lean_closure_set(x_34, 7, x_3);
lean_closure_set(x_34, 8, x_14);
lean_closure_set(x_34, 9, x_15);
lean_closure_set(x_34, 10, x_16);
lean_closure_set(x_34, 11, x_31);
lean_closure_set(x_34, 12, x_2);
lean_closure_set(x_34, 13, x_17);
lean_closure_set(x_34, 14, x_5);
lean_closure_set(x_34, 15, x_18);
lean_closure_set(x_34, 16, x_19);
lean_closure_set(x_34, 17, x_32);
lean_closure_set(x_34, 18, x_33);
lean_closure_set(x_34, 19, x_22);
lean_closure_set(x_34, 20, x_9);
lean_closure_set(x_34, 21, x_23);
lean_closure_set(x_34, 22, x_24);
lean_closure_set(x_34, 23, x_25);
lean_closure_set(x_34, 24, x_26);
x_35 = l_Lean_Meta_lambdaTelescope___redArg(x_14, x_5, x_27, x_29, x_30);
x_36 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_35, x_34);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
_start:
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_unbox(x_20);
x_30 = lean_unbox(x_21);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_29, x_30, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_box(x_19);
x_30 = lean_box(x_20);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_3);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 28, 27);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_4);
lean_closure_set(x_31, 4, x_5);
lean_closure_set(x_31, 5, x_6);
lean_closure_set(x_31, 6, x_7);
lean_closure_set(x_31, 7, x_8);
lean_closure_set(x_31, 8, x_9);
lean_closure_set(x_31, 9, x_10);
lean_closure_set(x_31, 10, x_28);
lean_closure_set(x_31, 11, x_11);
lean_closure_set(x_31, 12, x_12);
lean_closure_set(x_31, 13, x_13);
lean_closure_set(x_31, 14, x_14);
lean_closure_set(x_31, 15, x_15);
lean_closure_set(x_31, 16, x_16);
lean_closure_set(x_31, 17, x_17);
lean_closure_set(x_31, 18, x_18);
lean_closure_set(x_31, 19, x_29);
lean_closure_set(x_31, 20, x_30);
lean_closure_set(x_31, 21, x_21);
lean_closure_set(x_31, 22, x_22);
lean_closure_set(x_31, 23, x_23);
lean_closure_set(x_31, 24, x_24);
lean_closure_set(x_31, 25, x_25);
lean_closure_set(x_31, 26, x_26);
x_32 = lean_array_size(x_8);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_27, x_32, x_33, x_8);
x_35 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_34, x_31);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
_start:
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_unbox(x_19);
x_30 = lean_unbox(x_20);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_29, x_30, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_box(x_19);
x_30 = lean_box(x_20);
lean_inc(x_26);
lean_inc_ref(x_5);
lean_inc(x_3);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed), 28, 27);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_4);
lean_closure_set(x_31, 4, x_5);
lean_closure_set(x_31, 5, x_6);
lean_closure_set(x_31, 6, x_7);
lean_closure_set(x_31, 7, x_8);
lean_closure_set(x_31, 8, x_9);
lean_closure_set(x_31, 9, x_10);
lean_closure_set(x_31, 10, x_11);
lean_closure_set(x_31, 11, x_12);
lean_closure_set(x_31, 12, x_13);
lean_closure_set(x_31, 13, x_14);
lean_closure_set(x_31, 14, x_15);
lean_closure_set(x_31, 15, x_16);
lean_closure_set(x_31, 16, x_17);
lean_closure_set(x_31, 17, x_18);
lean_closure_set(x_31, 18, x_29);
lean_closure_set(x_31, 19, x_30);
lean_closure_set(x_31, 20, x_21);
lean_closure_set(x_31, 21, x_22);
lean_closure_set(x_31, 22, x_28);
lean_closure_set(x_31, 23, x_23);
lean_closure_set(x_31, 24, x_24);
lean_closure_set(x_31, 25, x_25);
lean_closure_set(x_31, 26, x_26);
x_32 = lean_array_size(x_27);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_26, x_32, x_33, x_27);
x_35 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_34, x_31);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
_start:
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_unbox(x_19);
x_30 = lean_unbox(x_20);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__66(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_29, x_30, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_2, x_3, x_13);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
x_17 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_16);
x_18 = lean_apply_2(x_6, lean_box(0), x_17);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_28);
lean_inc(x_22);
x_29 = l_Lean_isCasesOnRecursor(x_20, x_22);
x_30 = lean_box(x_14);
x_31 = lean_box(x_29);
lean_inc(x_22);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed), 28, 27);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_4);
lean_closure_set(x_32, 3, x_21);
lean_closure_set(x_32, 4, x_5);
lean_closure_set(x_32, 5, x_6);
lean_closure_set(x_32, 6, x_7);
lean_closure_set(x_32, 7, x_26);
lean_closure_set(x_32, 8, x_8);
lean_closure_set(x_32, 9, x_22);
lean_closure_set(x_32, 10, x_9);
lean_closure_set(x_32, 11, x_28);
lean_closure_set(x_32, 12, x_10);
lean_closure_set(x_32, 13, x_27);
lean_closure_set(x_32, 14, x_11);
lean_closure_set(x_32, 15, x_12);
lean_closure_set(x_32, 16, x_13);
lean_closure_set(x_32, 17, x_1);
lean_closure_set(x_32, 18, x_30);
lean_closure_set(x_32, 19, x_31);
lean_closure_set(x_32, 20, x_15);
lean_closure_set(x_32, 21, x_16);
lean_closure_set(x_32, 22, x_17);
lean_closure_set(x_32, 23, x_23);
lean_closure_set(x_32, 24, x_25);
lean_closure_set(x_32, 25, x_18);
lean_closure_set(x_32, 26, x_24);
if (x_29 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__67), 2, 1);
lean_closure_set(x_33, 0, x_32);
lean_inc_ref(x_33);
lean_inc(x_4);
lean_inc_ref(x_5);
lean_inc(x_22);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed), 8, 7);
lean_closure_set(x_34, 0, x_22);
lean_closure_set(x_34, 1, x_5);
lean_closure_set(x_34, 2, x_8);
lean_closure_set(x_34, 3, x_4);
lean_closure_set(x_34, 4, x_33);
lean_closure_set(x_34, 5, x_2);
lean_closure_set(x_34, 6, x_33);
x_35 = l_Lean_Meta_getMatcherInfo_x3f___redArg(x_5, x_19, x_22);
x_36 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_35, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__67), 2, 1);
lean_closure_set(x_37, 0, x_32);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_apply_2(x_2, lean_box(0), x_38);
x_40 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_39, x_37);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
x_22 = l_Lean_Meta_MatcherApp_transform___redArg___lam__70(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc_ref(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_18);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(x_20, 0, x_16);
lean_inc(x_16);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(x_21, 0, x_16);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 6, 3);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_1);
x_23 = lean_box(x_8);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_16);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed), 7, 4);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_1);
x_25 = lean_box(x_7);
lean_inc(x_14);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed), 20, 19);
lean_closure_set(x_26, 0, x_6);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_14);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_24);
lean_closure_set(x_26, 6, x_10);
lean_closure_set(x_26, 7, x_4);
lean_closure_set(x_26, 8, x_12);
lean_closure_set(x_26, 9, x_2);
lean_closure_set(x_26, 10, x_20);
lean_closure_set(x_26, 11, x_11);
lean_closure_set(x_26, 12, x_19);
lean_closure_set(x_26, 13, x_25);
lean_closure_set(x_26, 14, x_21);
lean_closure_set(x_26, 15, x_17);
lean_closure_set(x_26, 16, x_22);
lean_closure_set(x_26, 17, x_9);
lean_closure_set(x_26, 18, x_5);
x_27 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_7);
x_14 = lean_unbox(x_8);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_MatcherApp_transform___redArg(x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_11);
x_18 = lean_unbox(x_12);
x_19 = l_Lean_Meta_MatcherApp_transform(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_11);
lean_ctor_set(x_27, 3, x_10);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_14);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_10);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_52);
x_62 = l_Lean_FileMap_toPosition(x_52, x_54);
lean_dec(x_54);
x_63 = l_Lean_FileMap_toPosition(x_52, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (x_55 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_65;
x_11 = x_64;
x_12 = x_61;
x_13 = x_51;
x_14 = x_62;
x_15 = x_53;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_51);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_65;
x_11 = x_64;
x_12 = x_61;
x_13 = x_51;
x_14 = x_62;
x_15 = x_53;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_52);
x_69 = l_Lean_FileMap_toPosition(x_52, x_54);
lean_dec(x_54);
x_70 = l_Lean_FileMap_toPosition(x_52, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (x_55 == 0)
{
lean_dec_ref(x_50);
x_10 = x_72;
x_11 = x_71;
x_12 = x_68;
x_13 = x_51;
x_14 = x_69;
x_15 = x_53;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_51);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_72;
x_11 = x_71;
x_12 = x_68;
x_13 = x_51;
x_14 = x_69;
x_15 = x_53;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_78, x_81);
lean_dec(x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_79;
x_52 = x_80;
x_53 = x_81;
x_54 = x_84;
x_55 = x_82;
x_56 = x_83;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_79;
x_52 = x_80;
x_53 = x_81;
x_54 = x_84;
x_55 = x_82;
x_56 = x_83;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_89);
lean_dec(x_89);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_92);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_95;
x_79 = x_90;
x_80 = x_91;
x_81 = x_92;
x_82 = x_93;
x_83 = x_94;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_95;
x_79 = x_90;
x_80 = x_91;
x_81 = x_92;
x_82 = x_93;
x_83 = x_94;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_102;
x_89 = x_101;
x_90 = x_103;
x_91 = x_104;
x_92 = x_106;
x_93 = x_105;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_102;
x_89 = x_101;
x_90 = x_103;
x_91 = x_104;
x_92 = x_106;
x_93 = x_105;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc_ref(x_111);
lean_inc_ref(x_110);
lean_inc(x_113);
x_101 = x_113;
x_102 = x_117;
x_103 = x_110;
x_104 = x_111;
x_105 = x_114;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_warningAsError;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(x_112, x_120);
lean_inc_ref(x_111);
lean_inc_ref(x_110);
lean_inc(x_113);
x_101 = x_113;
x_102 = x_117;
x_103 = x_110;
x_104 = x_111;
x_105 = x_114;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_11 = lean_infer_type(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = l_Lean_Meta_mkEq(x_3, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
lean_inc_ref(x_6);
x_16 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_14, x_15, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_24 = l_Lean_Expr_mvarId_x21(x_17);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_25 = l_Lean_Meta_Split_simpMatchTarget(x_24, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_26);
x_27 = l_Lean_MVarId_refl(x_26, x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_26);
x_18 = x_27;
goto block_23;
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_42; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_42 = l_Lean_Exception_isInterrupt(x_28);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_28);
x_29 = x_43;
goto block_41;
}
else
{
lean_dec(x_28);
x_29 = x_42;
goto block_41;
}
block_41:
{
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_inc(x_26);
lean_ctor_set(x_27, 0, x_26);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_inc_ref(x_8);
x_34 = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(x_33, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_35 = l_Lean_MVarId_admit(x_26, x_1, x_6, x_7, x_8, x_9);
x_18 = x_35;
goto block_23;
}
else
{
lean_dec(x_26);
x_18 = x_34;
goto block_23;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_36 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_inc(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_26);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc_ref(x_8);
x_39 = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(x_38, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_40 = l_Lean_MVarId_admit(x_26, x_1, x_6, x_7, x_8, x_9);
x_18 = x_40;
goto block_23;
}
else
{
lean_dec(x_26);
x_18 = x_39;
goto block_23;
}
}
}
else
{
lean_dec(x_26);
x_18 = x_27;
goto block_23;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
block_23:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l_Lean_Meta_mkEqMPR(x_17, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_16;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_4 = x_9;
x_5 = x_10;
goto block_8;
}
case 6:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_4 = x_11;
x_5 = x_12;
goto block_8;
}
case 10:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 1);
x_2 = x_13;
goto _start;
}
case 8:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_16);
if (x_19 == 0)
{
x_2 = x_17;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_21);
if (x_23 == 0)
{
x_2 = x_22;
goto _start;
}
else
{
return x_3;
}
}
case 11:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 2);
x_2 = x_25;
goto _start;
}
case 1:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = l_Lean_Expr_fvarId_x21(x_1);
x_29 = l_Lean_instBEqFVarId_beq(x_27, x_28);
lean_dec(x_28);
return x_29;
}
default: 
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
block_8:
{
uint8_t x_6; 
x_6 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_12, x_17);
lean_inc_ref(x_11);
lean_ctor_set(x_3, 1, x_18);
x_19 = lean_array_fget(x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
x_20 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_19, x_1);
if (x_20 == 0)
{
lean_dec(x_19);
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1;
lean_inc_ref(x_1);
x_23 = l_Lean_MessageData_ofExpr(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc_ref(x_2);
x_27 = l_Lean_MessageData_ofExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofExpr(x_19);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_32, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_4 = x_16;
goto _start;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_box(0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_36, x_41);
lean_inc_ref(x_35);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_37);
x_44 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_45 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(x_44, x_1);
if (x_45 == 0)
{
lean_dec(x_44);
x_3 = x_43;
x_4 = x_40;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1;
lean_inc_ref(x_1);
x_48 = l_Lean_MessageData_ofExpr(x_1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc_ref(x_2);
x_52 = l_Lean_MessageData_ofExpr(x_2);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_ofExpr(x_44);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_57, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_3 = x_43;
x_4 = x_40;
goto _start;
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = lean_infer_type(x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_sub(x_15, x_1);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc_ref(x_6);
x_18 = l_Array_toSubarray___redArg(x_6, x_17, x_16);
x_19 = l_Array_toSubarray___redArg(x_6, x_16, x_15);
x_20 = lean_box(0);
lean_inc(x_14);
x_21 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(x_14, x_2, x_19, x_20, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = l_Subarray_copy___redArg(x_18);
x_23 = l_Lean_Meta_mkLambdaFVars(x_22, x_14, x_3, x_4, x_3, x_4, x_5, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = 0;
x_13 = 1;
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_box(x_12);
x_16 = lean_box(x_10);
x_17 = lean_box(x_13);
lean_inc(x_14);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_14, x_18, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_4, x_3, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_22, x_3, x_20);
x_3 = x_24;
x_4 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_1);
x_16 = l_Lean_Meta_arrowDomainsN(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_9, x_18, x_2, x_3, x_2, x_3, x_19, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_array_size(x_4);
x_23 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
x_24 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_22, x_23, x_4, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_35 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_35) == 0)
{
x_26 = x_8;
x_27 = x_13;
x_28 = x_14;
x_29 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
x_37 = l_Lean_levelOne;
x_38 = lean_array_set(x_8, x_36, x_37);
x_26 = x_38;
x_27 = x_13;
x_28 = x_14;
x_29 = lean_box(0);
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_9);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_30);
x_32 = l_Lean_Meta_MatcherApp_toExpr(x_31);
x_33 = l_Lean_mkArrowN(x_17, x_32, x_27, x_28);
lean_dec(x_17);
return x_33;
}
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_20;
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
x_17 = lean_unbox(x_3);
x_18 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_7(x_1, x_2, x_3, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_push(x_4, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_array_push(x_4, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0;
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_19 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_37 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
x_44 = l_Lean_instInhabitedExpr;
x_45 = l_instInhabitedOfMonad___redArg(x_26, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_5(x_46, x_2, x_3, x_4, x_5, lean_box(0));
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 2);
x_50 = lean_ctor_get(x_28, 3);
x_51 = lean_ctor_get(x_28, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_52 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_53 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_48);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_54, 0, x_48);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_50);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_59, 0, x_49);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_26, 1, x_53);
lean_ctor_set(x_26, 0, x_60);
x_61 = l_Lean_instInhabitedExpr;
x_62 = l_instInhabitedOfMonad___redArg(x_26, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_5(x_63, x_2, x_3, x_4, x_5, lean_box(0));
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_26, 0);
lean_inc(x_65);
lean_dec(x_26);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 4);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_72 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_66);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_73, 0, x_66);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_66);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_77, 0, x_68);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_78, 0, x_67);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 5, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_72);
x_81 = l_Lean_instInhabitedExpr;
x_82 = l_instInhabitedOfMonad___redArg(x_80, x_81);
x_83 = lean_panic_fn(x_82, x_1);
x_84 = lean_apply_5(x_83, x_2, x_3, x_4, x_5, lean_box(0));
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 2);
x_87 = lean_ctor_get(x_10, 3);
x_88 = lean_ctor_get(x_10, 4);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_89 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_90 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_85);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_91, 0, x_85);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_95, 0, x_87);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_96, 0, x_86);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_94);
lean_ctor_set(x_8, 1, x_90);
lean_ctor_set(x_8, 0, x_97);
x_98 = l_ReaderT_instMonad___redArg(x_8);
x_99 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_99, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 4);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
x_106 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_107 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_101);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_108, 0, x_101);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_101);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_112, 0, x_103);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_113, 0, x_102);
if (lean_is_scalar(x_105)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_105;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set(x_114, 4, x_111);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
x_116 = l_Lean_instInhabitedExpr;
x_117 = l_instInhabitedOfMonad___redArg(x_115, x_116);
x_118 = lean_panic_fn(x_117, x_1);
x_119 = lean_apply_5(x_118, x_2, x_3, x_4, x_5, lean_box(0));
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_120 = lean_ctor_get(x_8, 0);
lean_inc(x_120);
lean_dec(x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_120, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 4);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
x_126 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_127 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_121);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_128, 0, x_121);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_121);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_131, 0, x_124);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_132, 0, x_123);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_133, 0, x_122);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_125;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_132);
lean_ctor_set(x_134, 4, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_127);
x_136 = l_ReaderT_instMonad___redArg(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 4);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
 x_143 = lean_box(0);
}
x_144 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_145 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_139);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_146, 0, x_139);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_147, 0, x_139);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_149, 0, x_142);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_150, 0, x_141);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_151, 0, x_140);
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_143;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_150);
lean_ctor_set(x_152, 4, x_149);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_145);
x_154 = l_Lean_instInhabitedExpr;
x_155 = l_instInhabitedOfMonad___redArg(x_153, x_154);
x_156 = lean_panic_fn(x_155, x_1);
x_157 = lean_apply_5(x_156, x_2, x_3, x_4, x_5, lean_box(0));
return x_157;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_28; 
x_17 = l_Array_append___redArg(x_1, x_2);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_28 = l_Lean_Meta_instantiateLambda(x_9, x_17, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_28) == 0)
{
x_18 = x_28;
goto block_27;
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_34 = l_Lean_Exception_isInterrupt(x_29);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_29);
x_30 = x_35;
goto block_33;
}
else
{
lean_dec(x_29);
x_30 = x_34;
goto block_33;
}
block_33:
{
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_28);
x_31 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_32 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_31, x_12, x_13, x_14, x_15);
x_18 = x_32;
goto block_27;
}
else
{
x_18 = x_28;
goto block_27;
}
}
}
block_27:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_20 = lean_apply_9(x_3, x_4, x_11, x_17, x_19, x_12, x_13, x_14, x_15, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Array_append___redArg(x_5, x_6);
x_23 = l_Array_append___redArg(x_22, x_2);
x_24 = l_Array_append___redArg(x_23, x_10);
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_24, x_21, x_7, x_8, x_7, x_8, x_25, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_24);
return x_26;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
return x_20;
}
}
else
{
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_7);
x_18 = lean_unbox(x_8);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_6);
x_18 = lean_box(x_7);
x_19 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_10);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_17);
lean_closure_set(x_19, 7, x_18);
lean_closure_set(x_19, 8, x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_11, x_20, x_19, x_6, x_6, x_12, x_13, x_14, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_5);
x_18 = lean_box(x_6);
x_19 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_10);
lean_closure_set(x_19, 5, x_17);
lean_closure_set(x_19, 6, x_18);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_11, x_20, x_19, x_5, x_5, x_12, x_13, x_14, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_22 = lean_array_get_size(x_12);
x_23 = lean_nat_dec_eq(x_22, x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_24 = l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3;
x_25 = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(x_24, x_14, x_15, x_16, x_17);
return x_25;
}
else
{
lean_object* x_26; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_26 = l_Lean_Meta_instantiateForall(x_2, x_12, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(x_5);
x_30 = lean_box(x_6);
x_31 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(x_31, 0, x_13);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_12);
lean_closure_set(x_31, 4, x_29);
lean_closure_set(x_31, 5, x_30);
lean_closure_set(x_31, 6, x_7);
lean_closure_set(x_31, 7, x_8);
lean_closure_set(x_31, 8, x_9);
if (x_10 == 0)
{
x_32 = x_27;
x_33 = x_14;
x_34 = x_15;
x_35 = x_16;
x_36 = x_17;
x_37 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2;
x_47 = lean_mk_empty_array_with_capacity(x_11);
x_48 = lean_array_push(x_47, x_46);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_49 = l_Lean_Meta_instantiateForall(x_27, x_48, x_14, x_15, x_16, x_17);
lean_dec_ref(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_32 = x_50;
x_33 = x_14;
x_34 = x_15;
x_35 = x_16;
x_36 = x_17;
x_37 = lean_box(0);
goto block_45;
}
else
{
lean_dec_ref(x_31);
lean_dec(x_28);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
return x_49;
}
}
block_45:
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_20);
if (lean_is_scalar(x_28)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_28;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_20);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
x_39 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_32, x_38, x_31, x_5, x_5, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_39) == 0)
{
if (x_21 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2));
x_42 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7;
x_43 = lean_array_push(x_42, x_40);
x_44 = l_Lean_Meta_mkAppM(x_41, x_43, x_33, x_34, x_35, x_36);
return x_44;
}
}
else
{
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
return x_39;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = lean_unbox(x_10);
x_22 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec_ref(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0;
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_19 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_37 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
x_44 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_45 = l_instInhabitedOfMonad___redArg(x_26, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_5(x_46, x_2, x_3, x_4, x_5, lean_box(0));
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 2);
x_50 = lean_ctor_get(x_28, 3);
x_51 = lean_ctor_get(x_28, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_52 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_53 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_48);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_54, 0, x_48);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_50);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_59, 0, x_49);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_26, 1, x_53);
lean_ctor_set(x_26, 0, x_60);
x_61 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_62 = l_instInhabitedOfMonad___redArg(x_26, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_5(x_63, x_2, x_3, x_4, x_5, lean_box(0));
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_26, 0);
lean_inc(x_65);
lean_dec(x_26);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 4);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_72 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_66);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_73, 0, x_66);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_66);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_77, 0, x_68);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_78, 0, x_67);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 5, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_72);
x_81 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_82 = l_instInhabitedOfMonad___redArg(x_80, x_81);
x_83 = lean_panic_fn(x_82, x_1);
x_84 = lean_apply_5(x_83, x_2, x_3, x_4, x_5, lean_box(0));
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 2);
x_87 = lean_ctor_get(x_10, 3);
x_88 = lean_ctor_get(x_10, 4);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_89 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_90 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_85);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_91, 0, x_85);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_95, 0, x_87);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_96, 0, x_86);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_94);
lean_ctor_set(x_8, 1, x_90);
lean_ctor_set(x_8, 0, x_97);
x_98 = l_ReaderT_instMonad___redArg(x_8);
x_99 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_99, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 4);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
x_106 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_107 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_101);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_108, 0, x_101);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_101);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_112, 0, x_103);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_113, 0, x_102);
if (lean_is_scalar(x_105)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_105;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set(x_114, 4, x_111);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
x_116 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_117 = l_instInhabitedOfMonad___redArg(x_115, x_116);
x_118 = lean_panic_fn(x_117, x_1);
x_119 = lean_apply_5(x_118, x_2, x_3, x_4, x_5, lean_box(0));
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_120 = lean_ctor_get(x_8, 0);
lean_inc(x_120);
lean_dec(x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_120, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 4);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
x_126 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
x_127 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(x_121);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_128, 0, x_121);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_121);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_131, 0, x_124);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_132, 0, x_123);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_133, 0, x_122);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_125;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_132);
lean_ctor_set(x_134, 4, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_127);
x_136 = l_ReaderT_instMonad___redArg(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 4);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
 x_143 = lean_box(0);
}
x_144 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
x_145 = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(x_139);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_146, 0, x_139);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_147, 0, x_139);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_149, 0, x_142);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_150, 0, x_141);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_151, 0, x_140);
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_143;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_150);
lean_ctor_set(x_152, 4, x_149);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_145);
x_154 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7;
x_155 = l_instInhabitedOfMonad___redArg(x_153, x_154);
x_156 = lean_panic_fn(x_155, x_1);
x_157 = lean_apply_5(x_156, x_2, x_3, x_4, x_5, lean_box(0));
return x_157;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_6, x_1);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_38, 1);
x_54 = lean_ctor_get(x_38, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
x_57 = lean_ctor_get(x_39, 2);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_7);
x_60 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_60, 0, x_59);
x_13 = x_60;
goto block_32;
}
else
{
uint8_t x_61; 
lean_inc(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
x_61 = !lean_is_exclusive(x_39);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_ctor_get(x_39, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_39, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_39, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
x_67 = lean_ctor_get(x_50, 2);
x_68 = lean_array_fget(x_55, x_56);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_56, x_69);
lean_dec(x_56);
lean_ctor_set(x_39, 1, x_70);
x_71 = lean_nat_dec_lt(x_66, x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_7);
x_73 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_73, 0, x_72);
x_13 = x_73;
goto block_32;
}
else
{
uint8_t x_74; 
lean_inc(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
x_74 = !lean_is_exclusive(x_50);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_ctor_get(x_50, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_50, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_50, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_47, 0);
x_79 = lean_ctor_get(x_47, 1);
x_80 = lean_ctor_get(x_47, 2);
x_81 = lean_array_fget(x_65, x_66);
x_82 = lean_nat_add(x_66, x_69);
lean_dec(x_66);
lean_ctor_set(x_50, 1, x_82);
x_83 = lean_nat_dec_lt(x_79, x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_68);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_7);
x_85 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_85, 0, x_84);
x_13 = x_85;
goto block_32;
}
else
{
uint8_t x_86; 
lean_inc(x_80);
lean_inc(x_79);
lean_inc_ref(x_78);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_47, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_47, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_47, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_44, 0);
x_91 = lean_ctor_get(x_44, 1);
x_92 = lean_ctor_get(x_44, 2);
x_93 = lean_array_fget(x_78, x_79);
x_94 = lean_nat_add(x_79, x_69);
lean_dec(x_79);
lean_ctor_set(x_47, 1, x_94);
x_95 = lean_nat_dec_lt(x_91, x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_81);
lean_dec(x_68);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_7);
x_97 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_97, 0, x_96);
x_13 = x_97;
goto block_32;
}
else
{
uint8_t x_98; 
lean_inc(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_98 = !lean_is_exclusive(x_44);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_ctor_get(x_44, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_44, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_44, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_41, 0);
x_103 = lean_ctor_get(x_41, 1);
x_104 = lean_ctor_get(x_41, 2);
x_105 = lean_array_fget(x_90, x_91);
x_106 = lean_nat_add(x_91, x_69);
lean_dec(x_91);
lean_ctor_set(x_44, 1, x_106);
x_107 = lean_nat_dec_lt(x_103, x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_105);
lean_dec(x_93);
lean_dec(x_81);
lean_dec(x_68);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_7);
x_109 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_109, 0, x_108);
x_13 = x_109;
goto block_32;
}
else
{
uint8_t x_110; 
lean_inc(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_free_object(x_38);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
x_110 = !lean_is_exclusive(x_41);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_41, 2);
lean_dec(x_111);
x_112 = lean_ctor_get(x_41, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_41, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_105, 1);
x_115 = lean_ctor_get_uint8(x_105, sizeof(void*)*2);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_dec_eq(x_114, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_free_object(x_41);
lean_dec_ref(x_44);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_47);
lean_dec(x_93);
lean_dec_ref(x_50);
lean_dec(x_81);
lean_dec_ref(x_39);
lean_dec(x_68);
lean_dec(x_53);
x_118 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_119 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_119, 0, x_118);
x_13 = x_119;
goto block_32;
}
else
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = 0;
x_121 = lean_array_fget_borrowed(x_102, x_103);
x_122 = lean_box(x_120);
x_123 = lean_box(x_3);
x_124 = lean_box(x_115);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_121);
lean_inc(x_6);
lean_inc_ref(x_2);
x_125 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_125, 0, x_93);
lean_closure_set(x_125, 1, x_68);
lean_closure_set(x_125, 2, x_2);
lean_closure_set(x_125, 3, x_6);
lean_closure_set(x_125, 4, x_122);
lean_closure_set(x_125, 5, x_123);
lean_closure_set(x_125, 6, x_121);
lean_closure_set(x_125, 7, x_4);
lean_closure_set(x_125, 8, x_5);
lean_closure_set(x_125, 9, x_124);
lean_closure_set(x_125, 10, x_69);
x_126 = lean_nat_add(x_103, x_69);
lean_dec(x_103);
lean_ctor_set(x_41, 1, x_126);
x_127 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_127, 0, x_81);
lean_closure_set(x_127, 1, x_105);
lean_closure_set(x_127, 2, x_125);
lean_closure_set(x_127, 3, x_53);
lean_closure_set(x_127, 4, x_39);
lean_closure_set(x_127, 5, x_50);
lean_closure_set(x_127, 6, x_47);
lean_closure_set(x_127, 7, x_44);
lean_closure_set(x_127, 8, x_41);
x_13 = x_127;
goto block_32;
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_41);
x_128 = lean_ctor_get(x_105, 1);
x_129 = lean_ctor_get_uint8(x_105, sizeof(void*)*2);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_dec_eq(x_128, x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_44);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_47);
lean_dec(x_93);
lean_dec_ref(x_50);
lean_dec(x_81);
lean_dec_ref(x_39);
lean_dec(x_68);
lean_dec(x_53);
x_132 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_133 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_133, 0, x_132);
x_13 = x_133;
goto block_32;
}
else
{
uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_134 = 0;
x_135 = lean_array_fget_borrowed(x_102, x_103);
x_136 = lean_box(x_134);
x_137 = lean_box(x_3);
x_138 = lean_box(x_129);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_135);
lean_inc(x_6);
lean_inc_ref(x_2);
x_139 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_139, 0, x_93);
lean_closure_set(x_139, 1, x_68);
lean_closure_set(x_139, 2, x_2);
lean_closure_set(x_139, 3, x_6);
lean_closure_set(x_139, 4, x_136);
lean_closure_set(x_139, 5, x_137);
lean_closure_set(x_139, 6, x_135);
lean_closure_set(x_139, 7, x_4);
lean_closure_set(x_139, 8, x_5);
lean_closure_set(x_139, 9, x_138);
lean_closure_set(x_139, 10, x_69);
x_140 = lean_nat_add(x_103, x_69);
lean_dec(x_103);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_102);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_104);
x_142 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_142, 0, x_81);
lean_closure_set(x_142, 1, x_105);
lean_closure_set(x_142, 2, x_139);
lean_closure_set(x_142, 3, x_53);
lean_closure_set(x_142, 4, x_39);
lean_closure_set(x_142, 5, x_50);
lean_closure_set(x_142, 6, x_47);
lean_closure_set(x_142, 7, x_44);
lean_closure_set(x_142, 8, x_141);
x_13 = x_142;
goto block_32;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_44);
x_143 = lean_ctor_get(x_41, 0);
x_144 = lean_ctor_get(x_41, 1);
x_145 = lean_ctor_get(x_41, 2);
x_146 = lean_array_fget(x_90, x_91);
x_147 = lean_nat_add(x_91, x_69);
lean_dec(x_91);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_90);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_92);
x_149 = lean_nat_dec_lt(x_144, x_145);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_146);
lean_dec(x_93);
lean_dec(x_81);
lean_dec(x_68);
lean_ctor_set(x_35, 0, x_148);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_7);
x_151 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_151, 0, x_150);
x_13 = x_151;
goto block_32;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; uint8_t x_156; 
lean_inc(x_145);
lean_inc(x_144);
lean_inc_ref(x_143);
lean_free_object(x_38);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_152 = x_41;
} else {
 lean_dec_ref(x_41);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_146, 1);
x_154 = lean_ctor_get_uint8(x_146, sizeof(void*)*2);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_nat_dec_eq(x_153, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_152);
lean_dec_ref(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_47);
lean_dec(x_93);
lean_dec_ref(x_50);
lean_dec(x_81);
lean_dec_ref(x_39);
lean_dec(x_68);
lean_dec(x_53);
x_157 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_158 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_158, 0, x_157);
x_13 = x_158;
goto block_32;
}
else
{
uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_159 = 0;
x_160 = lean_array_fget_borrowed(x_143, x_144);
x_161 = lean_box(x_159);
x_162 = lean_box(x_3);
x_163 = lean_box(x_154);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_160);
lean_inc(x_6);
lean_inc_ref(x_2);
x_164 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_164, 0, x_93);
lean_closure_set(x_164, 1, x_68);
lean_closure_set(x_164, 2, x_2);
lean_closure_set(x_164, 3, x_6);
lean_closure_set(x_164, 4, x_161);
lean_closure_set(x_164, 5, x_162);
lean_closure_set(x_164, 6, x_160);
lean_closure_set(x_164, 7, x_4);
lean_closure_set(x_164, 8, x_5);
lean_closure_set(x_164, 9, x_163);
lean_closure_set(x_164, 10, x_69);
x_165 = lean_nat_add(x_144, x_69);
lean_dec(x_144);
if (lean_is_scalar(x_152)) {
 x_166 = lean_alloc_ctor(0, 3, 0);
} else {
 x_166 = x_152;
}
lean_ctor_set(x_166, 0, x_143);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_145);
x_167 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_167, 0, x_81);
lean_closure_set(x_167, 1, x_146);
lean_closure_set(x_167, 2, x_164);
lean_closure_set(x_167, 3, x_53);
lean_closure_set(x_167, 4, x_39);
lean_closure_set(x_167, 5, x_50);
lean_closure_set(x_167, 6, x_47);
lean_closure_set(x_167, 7, x_148);
lean_closure_set(x_167, 8, x_166);
x_13 = x_167;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_47);
x_168 = lean_ctor_get(x_44, 0);
x_169 = lean_ctor_get(x_44, 1);
x_170 = lean_ctor_get(x_44, 2);
x_171 = lean_array_fget(x_78, x_79);
x_172 = lean_nat_add(x_79, x_69);
lean_dec(x_79);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_78);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_80);
x_174 = lean_nat_dec_lt(x_169, x_170);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_171);
lean_dec(x_81);
lean_dec(x_68);
lean_ctor_set(x_36, 0, x_173);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_7);
x_176 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_176, 0, x_175);
x_13 = x_176;
goto block_32;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_170);
lean_inc(x_169);
lean_inc_ref(x_168);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_177 = x_44;
} else {
 lean_dec_ref(x_44);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_41, 0);
x_179 = lean_ctor_get(x_41, 1);
x_180 = lean_ctor_get(x_41, 2);
x_181 = lean_array_fget(x_168, x_169);
x_182 = lean_nat_add(x_169, x_69);
lean_dec(x_169);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 3, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_168);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_170);
x_184 = lean_nat_dec_lt(x_179, x_180);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_181);
lean_dec(x_171);
lean_dec(x_81);
lean_dec(x_68);
lean_ctor_set(x_36, 0, x_173);
lean_ctor_set(x_35, 0, x_183);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_7);
x_186 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_186, 0, x_185);
x_13 = x_186;
goto block_32;
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; uint8_t x_191; 
lean_inc(x_180);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_free_object(x_38);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_187 = x_41;
} else {
 lean_dec_ref(x_41);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_181, 1);
x_189 = lean_ctor_get_uint8(x_181, sizeof(void*)*2);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_nat_dec_eq(x_188, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
lean_dec_ref(x_183);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec_ref(x_50);
lean_dec(x_81);
lean_dec_ref(x_39);
lean_dec(x_68);
lean_dec(x_53);
x_192 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_193 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_193, 0, x_192);
x_13 = x_193;
goto block_32;
}
else
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = 0;
x_195 = lean_array_fget_borrowed(x_178, x_179);
x_196 = lean_box(x_194);
x_197 = lean_box(x_3);
x_198 = lean_box(x_189);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_195);
lean_inc(x_6);
lean_inc_ref(x_2);
x_199 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_199, 0, x_171);
lean_closure_set(x_199, 1, x_68);
lean_closure_set(x_199, 2, x_2);
lean_closure_set(x_199, 3, x_6);
lean_closure_set(x_199, 4, x_196);
lean_closure_set(x_199, 5, x_197);
lean_closure_set(x_199, 6, x_195);
lean_closure_set(x_199, 7, x_4);
lean_closure_set(x_199, 8, x_5);
lean_closure_set(x_199, 9, x_198);
lean_closure_set(x_199, 10, x_69);
x_200 = lean_nat_add(x_179, x_69);
lean_dec(x_179);
if (lean_is_scalar(x_187)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_187;
}
lean_ctor_set(x_201, 0, x_178);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_180);
x_202 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_202, 0, x_81);
lean_closure_set(x_202, 1, x_181);
lean_closure_set(x_202, 2, x_199);
lean_closure_set(x_202, 3, x_53);
lean_closure_set(x_202, 4, x_39);
lean_closure_set(x_202, 5, x_50);
lean_closure_set(x_202, 6, x_173);
lean_closure_set(x_202, 7, x_183);
lean_closure_set(x_202, 8, x_201);
x_13 = x_202;
goto block_32;
}
}
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_50);
x_203 = lean_ctor_get(x_47, 0);
x_204 = lean_ctor_get(x_47, 1);
x_205 = lean_ctor_get(x_47, 2);
x_206 = lean_array_fget(x_65, x_66);
x_207 = lean_nat_add(x_66, x_69);
lean_dec(x_66);
x_208 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_208, 0, x_65);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_67);
x_209 = lean_nat_dec_lt(x_204, x_205);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_206);
lean_dec(x_68);
lean_ctor_set(x_37, 0, x_208);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_7);
x_211 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_211, 0, x_210);
x_13 = x_211;
goto block_32;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc_ref(x_203);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_212 = x_47;
} else {
 lean_dec_ref(x_47);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_44, 0);
x_214 = lean_ctor_get(x_44, 1);
x_215 = lean_ctor_get(x_44, 2);
x_216 = lean_array_fget(x_203, x_204);
x_217 = lean_nat_add(x_204, x_69);
lean_dec(x_204);
if (lean_is_scalar(x_212)) {
 x_218 = lean_alloc_ctor(0, 3, 0);
} else {
 x_218 = x_212;
}
lean_ctor_set(x_218, 0, x_203);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_205);
x_219 = lean_nat_dec_lt(x_214, x_215);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_216);
lean_dec(x_206);
lean_dec(x_68);
lean_ctor_set(x_37, 0, x_208);
lean_ctor_set(x_36, 0, x_218);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_7);
x_221 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_221, 0, x_220);
x_13 = x_221;
goto block_32;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_inc(x_215);
lean_inc(x_214);
lean_inc_ref(x_213);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_222 = x_44;
} else {
 lean_dec_ref(x_44);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_41, 0);
x_224 = lean_ctor_get(x_41, 1);
x_225 = lean_ctor_get(x_41, 2);
x_226 = lean_array_fget(x_213, x_214);
x_227 = lean_nat_add(x_214, x_69);
lean_dec(x_214);
if (lean_is_scalar(x_222)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_222;
}
lean_ctor_set(x_228, 0, x_213);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_228, 2, x_215);
x_229 = lean_nat_dec_lt(x_224, x_225);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_226);
lean_dec(x_216);
lean_dec(x_206);
lean_dec(x_68);
lean_ctor_set(x_37, 0, x_208);
lean_ctor_set(x_36, 0, x_218);
lean_ctor_set(x_35, 0, x_228);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_7);
x_231 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_231, 0, x_230);
x_13 = x_231;
goto block_32;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
lean_inc(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
lean_free_object(x_38);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_232 = x_41;
} else {
 lean_dec_ref(x_41);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_226, 1);
x_234 = lean_ctor_get_uint8(x_226, sizeof(void*)*2);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_nat_dec_eq(x_233, x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_232);
lean_dec_ref(x_228);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_208);
lean_dec(x_206);
lean_dec_ref(x_39);
lean_dec(x_68);
lean_dec(x_53);
x_237 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_238 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_238, 0, x_237);
x_13 = x_238;
goto block_32;
}
else
{
uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_239 = 0;
x_240 = lean_array_fget_borrowed(x_223, x_224);
x_241 = lean_box(x_239);
x_242 = lean_box(x_3);
x_243 = lean_box(x_234);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_240);
lean_inc(x_6);
lean_inc_ref(x_2);
x_244 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_244, 0, x_216);
lean_closure_set(x_244, 1, x_68);
lean_closure_set(x_244, 2, x_2);
lean_closure_set(x_244, 3, x_6);
lean_closure_set(x_244, 4, x_241);
lean_closure_set(x_244, 5, x_242);
lean_closure_set(x_244, 6, x_240);
lean_closure_set(x_244, 7, x_4);
lean_closure_set(x_244, 8, x_5);
lean_closure_set(x_244, 9, x_243);
lean_closure_set(x_244, 10, x_69);
x_245 = lean_nat_add(x_224, x_69);
lean_dec(x_224);
if (lean_is_scalar(x_232)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_232;
}
lean_ctor_set(x_246, 0, x_223);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_225);
x_247 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_247, 0, x_206);
lean_closure_set(x_247, 1, x_226);
lean_closure_set(x_247, 2, x_244);
lean_closure_set(x_247, 3, x_53);
lean_closure_set(x_247, 4, x_39);
lean_closure_set(x_247, 5, x_208);
lean_closure_set(x_247, 6, x_218);
lean_closure_set(x_247, 7, x_228);
lean_closure_set(x_247, 8, x_246);
x_13 = x_247;
goto block_32;
}
}
}
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_39);
x_248 = lean_ctor_get(x_50, 0);
x_249 = lean_ctor_get(x_50, 1);
x_250 = lean_ctor_get(x_50, 2);
x_251 = lean_array_fget(x_55, x_56);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_add(x_56, x_252);
lean_dec(x_56);
x_254 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_254, 0, x_55);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_254, 2, x_57);
x_255 = lean_nat_dec_lt(x_249, x_250);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_251);
lean_ctor_set(x_38, 0, x_254);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_7);
x_257 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_257, 0, x_256);
x_13 = x_257;
goto block_32;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_inc(x_250);
lean_inc(x_249);
lean_inc_ref(x_248);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_258 = x_50;
} else {
 lean_dec_ref(x_50);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_47, 0);
x_260 = lean_ctor_get(x_47, 1);
x_261 = lean_ctor_get(x_47, 2);
x_262 = lean_array_fget(x_248, x_249);
x_263 = lean_nat_add(x_249, x_252);
lean_dec(x_249);
if (lean_is_scalar(x_258)) {
 x_264 = lean_alloc_ctor(0, 3, 0);
} else {
 x_264 = x_258;
}
lean_ctor_set(x_264, 0, x_248);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_250);
x_265 = lean_nat_dec_lt(x_260, x_261);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_262);
lean_dec(x_251);
lean_ctor_set(x_38, 0, x_254);
lean_ctor_set(x_37, 0, x_264);
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_7);
x_267 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_267, 0, x_266);
x_13 = x_267;
goto block_32;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_inc(x_261);
lean_inc(x_260);
lean_inc_ref(x_259);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_268 = x_47;
} else {
 lean_dec_ref(x_47);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_44, 0);
x_270 = lean_ctor_get(x_44, 1);
x_271 = lean_ctor_get(x_44, 2);
x_272 = lean_array_fget(x_259, x_260);
x_273 = lean_nat_add(x_260, x_252);
lean_dec(x_260);
if (lean_is_scalar(x_268)) {
 x_274 = lean_alloc_ctor(0, 3, 0);
} else {
 x_274 = x_268;
}
lean_ctor_set(x_274, 0, x_259);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_261);
x_275 = lean_nat_dec_lt(x_270, x_271);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_272);
lean_dec(x_262);
lean_dec(x_251);
lean_ctor_set(x_38, 0, x_254);
lean_ctor_set(x_37, 0, x_264);
lean_ctor_set(x_36, 0, x_274);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_7);
x_277 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_277, 0, x_276);
x_13 = x_277;
goto block_32;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_inc(x_271);
lean_inc(x_270);
lean_inc_ref(x_269);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_278 = x_44;
} else {
 lean_dec_ref(x_44);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_41, 0);
x_280 = lean_ctor_get(x_41, 1);
x_281 = lean_ctor_get(x_41, 2);
x_282 = lean_array_fget(x_269, x_270);
x_283 = lean_nat_add(x_270, x_252);
lean_dec(x_270);
if (lean_is_scalar(x_278)) {
 x_284 = lean_alloc_ctor(0, 3, 0);
} else {
 x_284 = x_278;
}
lean_ctor_set(x_284, 0, x_269);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_271);
x_285 = lean_nat_dec_lt(x_280, x_281);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_282);
lean_dec(x_272);
lean_dec(x_262);
lean_dec(x_251);
lean_ctor_set(x_38, 0, x_254);
lean_ctor_set(x_37, 0, x_264);
lean_ctor_set(x_36, 0, x_274);
lean_ctor_set(x_35, 0, x_284);
x_286 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_286, 0, x_7);
x_287 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_287, 0, x_286);
x_13 = x_287;
goto block_32;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; uint8_t x_292; 
lean_inc(x_281);
lean_inc(x_280);
lean_inc_ref(x_279);
lean_free_object(x_38);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_288 = x_41;
} else {
 lean_dec_ref(x_41);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_282, 1);
x_290 = lean_ctor_get_uint8(x_282, sizeof(void*)*2);
x_291 = lean_unsigned_to_nat(0u);
x_292 = lean_nat_dec_eq(x_289, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_288);
lean_dec_ref(x_284);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_274);
lean_dec(x_272);
lean_dec_ref(x_264);
lean_dec(x_262);
lean_dec_ref(x_254);
lean_dec(x_251);
lean_dec(x_53);
x_293 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_294 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_294, 0, x_293);
x_13 = x_294;
goto block_32;
}
else
{
uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_295 = 0;
x_296 = lean_array_fget_borrowed(x_279, x_280);
x_297 = lean_box(x_295);
x_298 = lean_box(x_3);
x_299 = lean_box(x_290);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_296);
lean_inc(x_6);
lean_inc_ref(x_2);
x_300 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_300, 0, x_272);
lean_closure_set(x_300, 1, x_251);
lean_closure_set(x_300, 2, x_2);
lean_closure_set(x_300, 3, x_6);
lean_closure_set(x_300, 4, x_297);
lean_closure_set(x_300, 5, x_298);
lean_closure_set(x_300, 6, x_296);
lean_closure_set(x_300, 7, x_4);
lean_closure_set(x_300, 8, x_5);
lean_closure_set(x_300, 9, x_299);
lean_closure_set(x_300, 10, x_252);
x_301 = lean_nat_add(x_280, x_252);
lean_dec(x_280);
if (lean_is_scalar(x_288)) {
 x_302 = lean_alloc_ctor(0, 3, 0);
} else {
 x_302 = x_288;
}
lean_ctor_set(x_302, 0, x_279);
lean_ctor_set(x_302, 1, x_301);
lean_ctor_set(x_302, 2, x_281);
x_303 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_303, 0, x_262);
lean_closure_set(x_303, 1, x_282);
lean_closure_set(x_303, 2, x_300);
lean_closure_set(x_303, 3, x_53);
lean_closure_set(x_303, 4, x_254);
lean_closure_set(x_303, 5, x_264);
lean_closure_set(x_303, 6, x_274);
lean_closure_set(x_303, 7, x_284);
lean_closure_set(x_303, 8, x_302);
x_13 = x_303;
goto block_32;
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
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_38, 1);
lean_inc(x_304);
lean_dec(x_38);
x_305 = lean_ctor_get(x_39, 0);
x_306 = lean_ctor_get(x_39, 1);
x_307 = lean_ctor_get(x_39, 2);
x_308 = lean_nat_dec_lt(x_306, x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_39);
lean_ctor_set(x_309, 1, x_304);
lean_ctor_set(x_37, 1, x_309);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_7);
x_311 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_311, 0, x_310);
x_13 = x_311;
goto block_32;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_inc(x_307);
lean_inc(x_306);
lean_inc_ref(x_305);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_312 = x_39;
} else {
 lean_dec_ref(x_39);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_50, 0);
x_314 = lean_ctor_get(x_50, 1);
x_315 = lean_ctor_get(x_50, 2);
x_316 = lean_array_fget(x_305, x_306);
x_317 = lean_unsigned_to_nat(1u);
x_318 = lean_nat_add(x_306, x_317);
lean_dec(x_306);
if (lean_is_scalar(x_312)) {
 x_319 = lean_alloc_ctor(0, 3, 0);
} else {
 x_319 = x_312;
}
lean_ctor_set(x_319, 0, x_305);
lean_ctor_set(x_319, 1, x_318);
lean_ctor_set(x_319, 2, x_307);
x_320 = lean_nat_dec_lt(x_314, x_315);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_316);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_304);
lean_ctor_set(x_37, 1, x_321);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_7);
x_323 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_323, 0, x_322);
x_13 = x_323;
goto block_32;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
lean_inc(x_315);
lean_inc(x_314);
lean_inc_ref(x_313);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_324 = x_50;
} else {
 lean_dec_ref(x_50);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_47, 0);
x_326 = lean_ctor_get(x_47, 1);
x_327 = lean_ctor_get(x_47, 2);
x_328 = lean_array_fget(x_313, x_314);
x_329 = lean_nat_add(x_314, x_317);
lean_dec(x_314);
if (lean_is_scalar(x_324)) {
 x_330 = lean_alloc_ctor(0, 3, 0);
} else {
 x_330 = x_324;
}
lean_ctor_set(x_330, 0, x_313);
lean_ctor_set(x_330, 1, x_329);
lean_ctor_set(x_330, 2, x_315);
x_331 = lean_nat_dec_lt(x_326, x_327);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_328);
lean_dec(x_316);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_319);
lean_ctor_set(x_332, 1, x_304);
lean_ctor_set(x_37, 1, x_332);
lean_ctor_set(x_37, 0, x_330);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_7);
x_334 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_334, 0, x_333);
x_13 = x_334;
goto block_32;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_inc(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_335 = x_47;
} else {
 lean_dec_ref(x_47);
 x_335 = lean_box(0);
}
x_336 = lean_ctor_get(x_44, 0);
x_337 = lean_ctor_get(x_44, 1);
x_338 = lean_ctor_get(x_44, 2);
x_339 = lean_array_fget(x_325, x_326);
x_340 = lean_nat_add(x_326, x_317);
lean_dec(x_326);
if (lean_is_scalar(x_335)) {
 x_341 = lean_alloc_ctor(0, 3, 0);
} else {
 x_341 = x_335;
}
lean_ctor_set(x_341, 0, x_325);
lean_ctor_set(x_341, 1, x_340);
lean_ctor_set(x_341, 2, x_327);
x_342 = lean_nat_dec_lt(x_337, x_338);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_339);
lean_dec(x_328);
lean_dec(x_316);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_319);
lean_ctor_set(x_343, 1, x_304);
lean_ctor_set(x_37, 1, x_343);
lean_ctor_set(x_37, 0, x_330);
lean_ctor_set(x_36, 0, x_341);
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_7);
x_345 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_345, 0, x_344);
x_13 = x_345;
goto block_32;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
lean_inc(x_338);
lean_inc(x_337);
lean_inc_ref(x_336);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_346 = x_44;
} else {
 lean_dec_ref(x_44);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_41, 0);
x_348 = lean_ctor_get(x_41, 1);
x_349 = lean_ctor_get(x_41, 2);
x_350 = lean_array_fget(x_336, x_337);
x_351 = lean_nat_add(x_337, x_317);
lean_dec(x_337);
if (lean_is_scalar(x_346)) {
 x_352 = lean_alloc_ctor(0, 3, 0);
} else {
 x_352 = x_346;
}
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set(x_352, 2, x_338);
x_353 = lean_nat_dec_lt(x_348, x_349);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_350);
lean_dec(x_339);
lean_dec(x_328);
lean_dec(x_316);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_319);
lean_ctor_set(x_354, 1, x_304);
lean_ctor_set(x_37, 1, x_354);
lean_ctor_set(x_37, 0, x_330);
lean_ctor_set(x_36, 0, x_341);
lean_ctor_set(x_35, 0, x_352);
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_7);
x_356 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_356, 0, x_355);
x_13 = x_356;
goto block_32;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
lean_inc(x_349);
lean_inc(x_348);
lean_inc_ref(x_347);
lean_free_object(x_37);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_357 = x_41;
} else {
 lean_dec_ref(x_41);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_350, 1);
x_359 = lean_ctor_get_uint8(x_350, sizeof(void*)*2);
x_360 = lean_unsigned_to_nat(0u);
x_361 = lean_nat_dec_eq(x_358, x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_357);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec_ref(x_341);
lean_dec(x_339);
lean_dec_ref(x_330);
lean_dec(x_328);
lean_dec_ref(x_319);
lean_dec(x_316);
lean_dec(x_304);
x_362 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_363 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_363, 0, x_362);
x_13 = x_363;
goto block_32;
}
else
{
uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = 0;
x_365 = lean_array_fget_borrowed(x_347, x_348);
x_366 = lean_box(x_364);
x_367 = lean_box(x_3);
x_368 = lean_box(x_359);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_365);
lean_inc(x_6);
lean_inc_ref(x_2);
x_369 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_369, 0, x_339);
lean_closure_set(x_369, 1, x_316);
lean_closure_set(x_369, 2, x_2);
lean_closure_set(x_369, 3, x_6);
lean_closure_set(x_369, 4, x_366);
lean_closure_set(x_369, 5, x_367);
lean_closure_set(x_369, 6, x_365);
lean_closure_set(x_369, 7, x_4);
lean_closure_set(x_369, 8, x_5);
lean_closure_set(x_369, 9, x_368);
lean_closure_set(x_369, 10, x_317);
x_370 = lean_nat_add(x_348, x_317);
lean_dec(x_348);
if (lean_is_scalar(x_357)) {
 x_371 = lean_alloc_ctor(0, 3, 0);
} else {
 x_371 = x_357;
}
lean_ctor_set(x_371, 0, x_347);
lean_ctor_set(x_371, 1, x_370);
lean_ctor_set(x_371, 2, x_349);
x_372 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_372, 0, x_328);
lean_closure_set(x_372, 1, x_350);
lean_closure_set(x_372, 2, x_369);
lean_closure_set(x_372, 3, x_304);
lean_closure_set(x_372, 4, x_319);
lean_closure_set(x_372, 5, x_330);
lean_closure_set(x_372, 6, x_341);
lean_closure_set(x_372, 7, x_352);
lean_closure_set(x_372, 8, x_371);
x_13 = x_372;
goto block_32;
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
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_373 = lean_ctor_get(x_37, 0);
lean_inc(x_373);
lean_dec(x_37);
x_374 = lean_ctor_get(x_38, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_375 = x_38;
} else {
 lean_dec_ref(x_38);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_39, 0);
x_377 = lean_ctor_get(x_39, 1);
x_378 = lean_ctor_get(x_39, 2);
x_379 = lean_nat_dec_lt(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
if (lean_is_scalar(x_375)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_375;
}
lean_ctor_set(x_380, 0, x_39);
lean_ctor_set(x_380, 1, x_374);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_373);
lean_ctor_set(x_381, 1, x_380);
lean_ctor_set(x_36, 1, x_381);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_7);
x_383 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_383, 0, x_382);
x_13 = x_383;
goto block_32;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
lean_inc(x_378);
lean_inc(x_377);
lean_inc_ref(x_376);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_384 = x_39;
} else {
 lean_dec_ref(x_39);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
x_386 = lean_ctor_get(x_373, 1);
x_387 = lean_ctor_get(x_373, 2);
x_388 = lean_array_fget(x_376, x_377);
x_389 = lean_unsigned_to_nat(1u);
x_390 = lean_nat_add(x_377, x_389);
lean_dec(x_377);
if (lean_is_scalar(x_384)) {
 x_391 = lean_alloc_ctor(0, 3, 0);
} else {
 x_391 = x_384;
}
lean_ctor_set(x_391, 0, x_376);
lean_ctor_set(x_391, 1, x_390);
lean_ctor_set(x_391, 2, x_378);
x_392 = lean_nat_dec_lt(x_386, x_387);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_388);
if (lean_is_scalar(x_375)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_375;
}
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_374);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_373);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_36, 1, x_394);
x_395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_395, 0, x_7);
x_396 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_396, 0, x_395);
x_13 = x_396;
goto block_32;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
lean_inc(x_387);
lean_inc(x_386);
lean_inc_ref(x_385);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 x_397 = x_373;
} else {
 lean_dec_ref(x_373);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_47, 0);
x_399 = lean_ctor_get(x_47, 1);
x_400 = lean_ctor_get(x_47, 2);
x_401 = lean_array_fget(x_385, x_386);
x_402 = lean_nat_add(x_386, x_389);
lean_dec(x_386);
if (lean_is_scalar(x_397)) {
 x_403 = lean_alloc_ctor(0, 3, 0);
} else {
 x_403 = x_397;
}
lean_ctor_set(x_403, 0, x_385);
lean_ctor_set(x_403, 1, x_402);
lean_ctor_set(x_403, 2, x_387);
x_404 = lean_nat_dec_lt(x_399, x_400);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_401);
lean_dec(x_388);
if (lean_is_scalar(x_375)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_375;
}
lean_ctor_set(x_405, 0, x_391);
lean_ctor_set(x_405, 1, x_374);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set(x_36, 1, x_406);
x_407 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_407, 0, x_7);
x_408 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_408, 0, x_407);
x_13 = x_408;
goto block_32;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
lean_inc(x_400);
lean_inc(x_399);
lean_inc_ref(x_398);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_409 = x_47;
} else {
 lean_dec_ref(x_47);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_44, 0);
x_411 = lean_ctor_get(x_44, 1);
x_412 = lean_ctor_get(x_44, 2);
x_413 = lean_array_fget(x_398, x_399);
x_414 = lean_nat_add(x_399, x_389);
lean_dec(x_399);
if (lean_is_scalar(x_409)) {
 x_415 = lean_alloc_ctor(0, 3, 0);
} else {
 x_415 = x_409;
}
lean_ctor_set(x_415, 0, x_398);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_415, 2, x_400);
x_416 = lean_nat_dec_lt(x_411, x_412);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_388);
if (lean_is_scalar(x_375)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_375;
}
lean_ctor_set(x_417, 0, x_391);
lean_ctor_set(x_417, 1, x_374);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_403);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set(x_36, 1, x_418);
lean_ctor_set(x_36, 0, x_415);
x_419 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_419, 0, x_7);
x_420 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_420, 0, x_419);
x_13 = x_420;
goto block_32;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
lean_inc(x_412);
lean_inc(x_411);
lean_inc_ref(x_410);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_421 = x_44;
} else {
 lean_dec_ref(x_44);
 x_421 = lean_box(0);
}
x_422 = lean_ctor_get(x_41, 0);
x_423 = lean_ctor_get(x_41, 1);
x_424 = lean_ctor_get(x_41, 2);
x_425 = lean_array_fget(x_410, x_411);
x_426 = lean_nat_add(x_411, x_389);
lean_dec(x_411);
if (lean_is_scalar(x_421)) {
 x_427 = lean_alloc_ctor(0, 3, 0);
} else {
 x_427 = x_421;
}
lean_ctor_set(x_427, 0, x_410);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_427, 2, x_412);
x_428 = lean_nat_dec_lt(x_423, x_424);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_388);
if (lean_is_scalar(x_375)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_375;
}
lean_ctor_set(x_429, 0, x_391);
lean_ctor_set(x_429, 1, x_374);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_403);
lean_ctor_set(x_430, 1, x_429);
lean_ctor_set(x_36, 1, x_430);
lean_ctor_set(x_36, 0, x_415);
lean_ctor_set(x_35, 0, x_427);
x_431 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_431, 0, x_7);
x_432 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_432, 0, x_431);
x_13 = x_432;
goto block_32;
}
else
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; uint8_t x_437; 
lean_inc(x_424);
lean_inc(x_423);
lean_inc_ref(x_422);
lean_dec(x_375);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_433 = x_41;
} else {
 lean_dec_ref(x_41);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_425, 1);
x_435 = lean_ctor_get_uint8(x_425, sizeof(void*)*2);
x_436 = lean_unsigned_to_nat(0u);
x_437 = lean_nat_dec_eq(x_434, x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_433);
lean_dec_ref(x_427);
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec_ref(x_415);
lean_dec(x_413);
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_391);
lean_dec(x_388);
lean_dec(x_374);
x_438 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_439 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_439, 0, x_438);
x_13 = x_439;
goto block_32;
}
else
{
uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_440 = 0;
x_441 = lean_array_fget_borrowed(x_422, x_423);
x_442 = lean_box(x_440);
x_443 = lean_box(x_3);
x_444 = lean_box(x_435);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_441);
lean_inc(x_6);
lean_inc_ref(x_2);
x_445 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_445, 0, x_413);
lean_closure_set(x_445, 1, x_388);
lean_closure_set(x_445, 2, x_2);
lean_closure_set(x_445, 3, x_6);
lean_closure_set(x_445, 4, x_442);
lean_closure_set(x_445, 5, x_443);
lean_closure_set(x_445, 6, x_441);
lean_closure_set(x_445, 7, x_4);
lean_closure_set(x_445, 8, x_5);
lean_closure_set(x_445, 9, x_444);
lean_closure_set(x_445, 10, x_389);
x_446 = lean_nat_add(x_423, x_389);
lean_dec(x_423);
if (lean_is_scalar(x_433)) {
 x_447 = lean_alloc_ctor(0, 3, 0);
} else {
 x_447 = x_433;
}
lean_ctor_set(x_447, 0, x_422);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set(x_447, 2, x_424);
x_448 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_448, 0, x_401);
lean_closure_set(x_448, 1, x_425);
lean_closure_set(x_448, 2, x_445);
lean_closure_set(x_448, 3, x_374);
lean_closure_set(x_448, 4, x_391);
lean_closure_set(x_448, 5, x_403);
lean_closure_set(x_448, 6, x_415);
lean_closure_set(x_448, 7, x_427);
lean_closure_set(x_448, 8, x_447);
x_13 = x_448;
goto block_32;
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
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_449 = lean_ctor_get(x_36, 0);
lean_inc(x_449);
lean_dec(x_36);
x_450 = lean_ctor_get(x_37, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_451 = x_37;
} else {
 lean_dec_ref(x_37);
 x_451 = lean_box(0);
}
x_452 = lean_ctor_get(x_38, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_453 = x_38;
} else {
 lean_dec_ref(x_38);
 x_453 = lean_box(0);
}
x_454 = lean_ctor_get(x_39, 0);
x_455 = lean_ctor_get(x_39, 1);
x_456 = lean_ctor_get(x_39, 2);
x_457 = lean_nat_dec_lt(x_455, x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
if (lean_is_scalar(x_453)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_453;
}
lean_ctor_set(x_458, 0, x_39);
lean_ctor_set(x_458, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_451;
}
lean_ctor_set(x_459, 0, x_450);
lean_ctor_set(x_459, 1, x_458);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_449);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set(x_35, 1, x_460);
x_461 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_461, 0, x_7);
x_462 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_462, 0, x_461);
x_13 = x_462;
goto block_32;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
lean_inc(x_456);
lean_inc(x_455);
lean_inc_ref(x_454);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_463 = x_39;
} else {
 lean_dec_ref(x_39);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_450, 0);
x_465 = lean_ctor_get(x_450, 1);
x_466 = lean_ctor_get(x_450, 2);
x_467 = lean_array_fget(x_454, x_455);
x_468 = lean_unsigned_to_nat(1u);
x_469 = lean_nat_add(x_455, x_468);
lean_dec(x_455);
if (lean_is_scalar(x_463)) {
 x_470 = lean_alloc_ctor(0, 3, 0);
} else {
 x_470 = x_463;
}
lean_ctor_set(x_470, 0, x_454);
lean_ctor_set(x_470, 1, x_469);
lean_ctor_set(x_470, 2, x_456);
x_471 = lean_nat_dec_lt(x_465, x_466);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_467);
if (lean_is_scalar(x_453)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_453;
}
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_451;
}
lean_ctor_set(x_473, 0, x_450);
lean_ctor_set(x_473, 1, x_472);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_449);
lean_ctor_set(x_474, 1, x_473);
lean_ctor_set(x_35, 1, x_474);
x_475 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_475, 0, x_7);
x_476 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_476, 0, x_475);
x_13 = x_476;
goto block_32;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
lean_inc(x_466);
lean_inc(x_465);
lean_inc_ref(x_464);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 lean_ctor_release(x_450, 2);
 x_477 = x_450;
} else {
 lean_dec_ref(x_450);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_449, 0);
x_479 = lean_ctor_get(x_449, 1);
x_480 = lean_ctor_get(x_449, 2);
x_481 = lean_array_fget(x_464, x_465);
x_482 = lean_nat_add(x_465, x_468);
lean_dec(x_465);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(0, 3, 0);
} else {
 x_483 = x_477;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set(x_483, 2, x_466);
x_484 = lean_nat_dec_lt(x_479, x_480);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_481);
lean_dec(x_467);
if (lean_is_scalar(x_453)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_453;
}
lean_ctor_set(x_485, 0, x_470);
lean_ctor_set(x_485, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_451;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_449);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_35, 1, x_487);
x_488 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_488, 0, x_7);
x_489 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_489, 0, x_488);
x_13 = x_489;
goto block_32;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
lean_inc(x_480);
lean_inc(x_479);
lean_inc_ref(x_478);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 lean_ctor_release(x_449, 2);
 x_490 = x_449;
} else {
 lean_dec_ref(x_449);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_44, 0);
x_492 = lean_ctor_get(x_44, 1);
x_493 = lean_ctor_get(x_44, 2);
x_494 = lean_array_fget(x_478, x_479);
x_495 = lean_nat_add(x_479, x_468);
lean_dec(x_479);
if (lean_is_scalar(x_490)) {
 x_496 = lean_alloc_ctor(0, 3, 0);
} else {
 x_496 = x_490;
}
lean_ctor_set(x_496, 0, x_478);
lean_ctor_set(x_496, 1, x_495);
lean_ctor_set(x_496, 2, x_480);
x_497 = lean_nat_dec_lt(x_492, x_493);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_494);
lean_dec(x_481);
lean_dec(x_467);
if (lean_is_scalar(x_453)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_453;
}
lean_ctor_set(x_498, 0, x_470);
lean_ctor_set(x_498, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_451;
}
lean_ctor_set(x_499, 0, x_483);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_496);
lean_ctor_set(x_500, 1, x_499);
lean_ctor_set(x_35, 1, x_500);
x_501 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_501, 0, x_7);
x_502 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_502, 0, x_501);
x_13 = x_502;
goto block_32;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
lean_inc(x_493);
lean_inc(x_492);
lean_inc_ref(x_491);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_503 = x_44;
} else {
 lean_dec_ref(x_44);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_41, 0);
x_505 = lean_ctor_get(x_41, 1);
x_506 = lean_ctor_get(x_41, 2);
x_507 = lean_array_fget(x_491, x_492);
x_508 = lean_nat_add(x_492, x_468);
lean_dec(x_492);
if (lean_is_scalar(x_503)) {
 x_509 = lean_alloc_ctor(0, 3, 0);
} else {
 x_509 = x_503;
}
lean_ctor_set(x_509, 0, x_491);
lean_ctor_set(x_509, 1, x_508);
lean_ctor_set(x_509, 2, x_493);
x_510 = lean_nat_dec_lt(x_505, x_506);
if (x_510 == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_507);
lean_dec(x_494);
lean_dec(x_481);
lean_dec(x_467);
if (lean_is_scalar(x_453)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_453;
}
lean_ctor_set(x_511, 0, x_470);
lean_ctor_set(x_511, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_451;
}
lean_ctor_set(x_512, 0, x_483);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_496);
lean_ctor_set(x_513, 1, x_512);
lean_ctor_set(x_35, 1, x_513);
lean_ctor_set(x_35, 0, x_509);
x_514 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_514, 0, x_7);
x_515 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_515, 0, x_514);
x_13 = x_515;
goto block_32;
}
else
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; uint8_t x_520; 
lean_inc(x_506);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_dec(x_453);
lean_dec(x_451);
lean_free_object(x_35);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_516 = x_41;
} else {
 lean_dec_ref(x_41);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_507, 1);
x_518 = lean_ctor_get_uint8(x_507, sizeof(void*)*2);
x_519 = lean_unsigned_to_nat(0u);
x_520 = lean_nat_dec_eq(x_517, x_519);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_516);
lean_dec_ref(x_509);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec_ref(x_496);
lean_dec(x_494);
lean_dec_ref(x_483);
lean_dec(x_481);
lean_dec_ref(x_470);
lean_dec(x_467);
lean_dec(x_452);
x_521 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_522 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_522, 0, x_521);
x_13 = x_522;
goto block_32;
}
else
{
uint8_t x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_523 = 0;
x_524 = lean_array_fget_borrowed(x_504, x_505);
x_525 = lean_box(x_523);
x_526 = lean_box(x_3);
x_527 = lean_box(x_518);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_524);
lean_inc(x_6);
lean_inc_ref(x_2);
x_528 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_528, 0, x_494);
lean_closure_set(x_528, 1, x_467);
lean_closure_set(x_528, 2, x_2);
lean_closure_set(x_528, 3, x_6);
lean_closure_set(x_528, 4, x_525);
lean_closure_set(x_528, 5, x_526);
lean_closure_set(x_528, 6, x_524);
lean_closure_set(x_528, 7, x_4);
lean_closure_set(x_528, 8, x_5);
lean_closure_set(x_528, 9, x_527);
lean_closure_set(x_528, 10, x_468);
x_529 = lean_nat_add(x_505, x_468);
lean_dec(x_505);
if (lean_is_scalar(x_516)) {
 x_530 = lean_alloc_ctor(0, 3, 0);
} else {
 x_530 = x_516;
}
lean_ctor_set(x_530, 0, x_504);
lean_ctor_set(x_530, 1, x_529);
lean_ctor_set(x_530, 2, x_506);
x_531 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_531, 0, x_481);
lean_closure_set(x_531, 1, x_507);
lean_closure_set(x_531, 2, x_528);
lean_closure_set(x_531, 3, x_452);
lean_closure_set(x_531, 4, x_470);
lean_closure_set(x_531, 5, x_483);
lean_closure_set(x_531, 6, x_496);
lean_closure_set(x_531, 7, x_509);
lean_closure_set(x_531, 8, x_530);
x_13 = x_531;
goto block_32;
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
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_532 = lean_ctor_get(x_35, 0);
lean_inc(x_532);
lean_dec(x_35);
x_533 = lean_ctor_get(x_36, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_534 = x_36;
} else {
 lean_dec_ref(x_36);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_37, 0);
lean_inc(x_535);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_536 = x_37;
} else {
 lean_dec_ref(x_37);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_38, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_538 = x_38;
} else {
 lean_dec_ref(x_38);
 x_538 = lean_box(0);
}
x_539 = lean_ctor_get(x_39, 0);
x_540 = lean_ctor_get(x_39, 1);
x_541 = lean_ctor_get(x_39, 2);
x_542 = lean_nat_dec_lt(x_540, x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
if (lean_is_scalar(x_538)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_538;
}
lean_ctor_set(x_543, 0, x_39);
lean_ctor_set(x_543, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_536;
}
lean_ctor_set(x_544, 0, x_535);
lean_ctor_set(x_544, 1, x_543);
if (lean_is_scalar(x_534)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_534;
}
lean_ctor_set(x_545, 0, x_533);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_532);
lean_ctor_set(x_546, 1, x_545);
lean_ctor_set(x_7, 1, x_546);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_7);
x_548 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_548, 0, x_547);
x_13 = x_548;
goto block_32;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
lean_inc(x_541);
lean_inc(x_540);
lean_inc_ref(x_539);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_549 = x_39;
} else {
 lean_dec_ref(x_39);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_535, 0);
x_551 = lean_ctor_get(x_535, 1);
x_552 = lean_ctor_get(x_535, 2);
x_553 = lean_array_fget(x_539, x_540);
x_554 = lean_unsigned_to_nat(1u);
x_555 = lean_nat_add(x_540, x_554);
lean_dec(x_540);
if (lean_is_scalar(x_549)) {
 x_556 = lean_alloc_ctor(0, 3, 0);
} else {
 x_556 = x_549;
}
lean_ctor_set(x_556, 0, x_539);
lean_ctor_set(x_556, 1, x_555);
lean_ctor_set(x_556, 2, x_541);
x_557 = lean_nat_dec_lt(x_551, x_552);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_553);
if (lean_is_scalar(x_538)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_538;
}
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_536;
}
lean_ctor_set(x_559, 0, x_535);
lean_ctor_set(x_559, 1, x_558);
if (lean_is_scalar(x_534)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_534;
}
lean_ctor_set(x_560, 0, x_533);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_532);
lean_ctor_set(x_561, 1, x_560);
lean_ctor_set(x_7, 1, x_561);
x_562 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_562, 0, x_7);
x_563 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_563, 0, x_562);
x_13 = x_563;
goto block_32;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; 
lean_inc(x_552);
lean_inc(x_551);
lean_inc_ref(x_550);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 lean_ctor_release(x_535, 2);
 x_564 = x_535;
} else {
 lean_dec_ref(x_535);
 x_564 = lean_box(0);
}
x_565 = lean_ctor_get(x_533, 0);
x_566 = lean_ctor_get(x_533, 1);
x_567 = lean_ctor_get(x_533, 2);
x_568 = lean_array_fget(x_550, x_551);
x_569 = lean_nat_add(x_551, x_554);
lean_dec(x_551);
if (lean_is_scalar(x_564)) {
 x_570 = lean_alloc_ctor(0, 3, 0);
} else {
 x_570 = x_564;
}
lean_ctor_set(x_570, 0, x_550);
lean_ctor_set(x_570, 1, x_569);
lean_ctor_set(x_570, 2, x_552);
x_571 = lean_nat_dec_lt(x_566, x_567);
if (x_571 == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_568);
lean_dec(x_553);
if (lean_is_scalar(x_538)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_538;
}
lean_ctor_set(x_572, 0, x_556);
lean_ctor_set(x_572, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_536;
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_572);
if (lean_is_scalar(x_534)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_534;
}
lean_ctor_set(x_574, 0, x_533);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_532);
lean_ctor_set(x_575, 1, x_574);
lean_ctor_set(x_7, 1, x_575);
x_576 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_576, 0, x_7);
x_577 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_577, 0, x_576);
x_13 = x_577;
goto block_32;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; 
lean_inc(x_567);
lean_inc(x_566);
lean_inc_ref(x_565);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 lean_ctor_release(x_533, 2);
 x_578 = x_533;
} else {
 lean_dec_ref(x_533);
 x_578 = lean_box(0);
}
x_579 = lean_ctor_get(x_532, 0);
x_580 = lean_ctor_get(x_532, 1);
x_581 = lean_ctor_get(x_532, 2);
x_582 = lean_array_fget(x_565, x_566);
x_583 = lean_nat_add(x_566, x_554);
lean_dec(x_566);
if (lean_is_scalar(x_578)) {
 x_584 = lean_alloc_ctor(0, 3, 0);
} else {
 x_584 = x_578;
}
lean_ctor_set(x_584, 0, x_565);
lean_ctor_set(x_584, 1, x_583);
lean_ctor_set(x_584, 2, x_567);
x_585 = lean_nat_dec_lt(x_580, x_581);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_582);
lean_dec(x_568);
lean_dec(x_553);
if (lean_is_scalar(x_538)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_538;
}
lean_ctor_set(x_586, 0, x_556);
lean_ctor_set(x_586, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_536;
}
lean_ctor_set(x_587, 0, x_570);
lean_ctor_set(x_587, 1, x_586);
if (lean_is_scalar(x_534)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_534;
}
lean_ctor_set(x_588, 0, x_584);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_532);
lean_ctor_set(x_589, 1, x_588);
lean_ctor_set(x_7, 1, x_589);
x_590 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_590, 0, x_7);
x_591 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_591, 0, x_590);
x_13 = x_591;
goto block_32;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; 
lean_inc(x_581);
lean_inc(x_580);
lean_inc_ref(x_579);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 lean_ctor_release(x_532, 2);
 x_592 = x_532;
} else {
 lean_dec_ref(x_532);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_41, 0);
x_594 = lean_ctor_get(x_41, 1);
x_595 = lean_ctor_get(x_41, 2);
x_596 = lean_array_fget(x_579, x_580);
x_597 = lean_nat_add(x_580, x_554);
lean_dec(x_580);
if (lean_is_scalar(x_592)) {
 x_598 = lean_alloc_ctor(0, 3, 0);
} else {
 x_598 = x_592;
}
lean_ctor_set(x_598, 0, x_579);
lean_ctor_set(x_598, 1, x_597);
lean_ctor_set(x_598, 2, x_581);
x_599 = lean_nat_dec_lt(x_594, x_595);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_596);
lean_dec(x_582);
lean_dec(x_568);
lean_dec(x_553);
if (lean_is_scalar(x_538)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_538;
}
lean_ctor_set(x_600, 0, x_556);
lean_ctor_set(x_600, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_536;
}
lean_ctor_set(x_601, 0, x_570);
lean_ctor_set(x_601, 1, x_600);
if (lean_is_scalar(x_534)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_534;
}
lean_ctor_set(x_602, 0, x_584);
lean_ctor_set(x_602, 1, x_601);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_598);
lean_ctor_set(x_603, 1, x_602);
lean_ctor_set(x_7, 1, x_603);
x_604 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_604, 0, x_7);
x_605 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_605, 0, x_604);
x_13 = x_605;
goto block_32;
}
else
{
lean_object* x_606; lean_object* x_607; uint8_t x_608; lean_object* x_609; uint8_t x_610; 
lean_inc(x_595);
lean_inc(x_594);
lean_inc_ref(x_593);
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_534);
lean_free_object(x_7);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_606 = x_41;
} else {
 lean_dec_ref(x_41);
 x_606 = lean_box(0);
}
x_607 = lean_ctor_get(x_596, 1);
x_608 = lean_ctor_get_uint8(x_596, sizeof(void*)*2);
x_609 = lean_unsigned_to_nat(0u);
x_610 = lean_nat_dec_eq(x_607, x_609);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; 
lean_dec(x_606);
lean_dec_ref(x_598);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec_ref(x_584);
lean_dec(x_582);
lean_dec_ref(x_570);
lean_dec(x_568);
lean_dec_ref(x_556);
lean_dec(x_553);
lean_dec(x_537);
x_611 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_612 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_612, 0, x_611);
x_13 = x_612;
goto block_32;
}
else
{
uint8_t x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_613 = 0;
x_614 = lean_array_fget_borrowed(x_593, x_594);
x_615 = lean_box(x_613);
x_616 = lean_box(x_3);
x_617 = lean_box(x_608);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_614);
lean_inc(x_6);
lean_inc_ref(x_2);
x_618 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_618, 0, x_582);
lean_closure_set(x_618, 1, x_553);
lean_closure_set(x_618, 2, x_2);
lean_closure_set(x_618, 3, x_6);
lean_closure_set(x_618, 4, x_615);
lean_closure_set(x_618, 5, x_616);
lean_closure_set(x_618, 6, x_614);
lean_closure_set(x_618, 7, x_4);
lean_closure_set(x_618, 8, x_5);
lean_closure_set(x_618, 9, x_617);
lean_closure_set(x_618, 10, x_554);
x_619 = lean_nat_add(x_594, x_554);
lean_dec(x_594);
if (lean_is_scalar(x_606)) {
 x_620 = lean_alloc_ctor(0, 3, 0);
} else {
 x_620 = x_606;
}
lean_ctor_set(x_620, 0, x_593);
lean_ctor_set(x_620, 1, x_619);
lean_ctor_set(x_620, 2, x_595);
x_621 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_621, 0, x_568);
lean_closure_set(x_621, 1, x_596);
lean_closure_set(x_621, 2, x_618);
lean_closure_set(x_621, 3, x_537);
lean_closure_set(x_621, 4, x_556);
lean_closure_set(x_621, 5, x_570);
lean_closure_set(x_621, 6, x_584);
lean_closure_set(x_621, 7, x_598);
lean_closure_set(x_621, 8, x_620);
x_13 = x_621;
goto block_32;
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
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_622 = lean_ctor_get(x_7, 0);
lean_inc(x_622);
lean_dec(x_7);
x_623 = lean_ctor_get(x_35, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_624 = x_35;
} else {
 lean_dec_ref(x_35);
 x_624 = lean_box(0);
}
x_625 = lean_ctor_get(x_36, 0);
lean_inc(x_625);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_626 = x_36;
} else {
 lean_dec_ref(x_36);
 x_626 = lean_box(0);
}
x_627 = lean_ctor_get(x_37, 0);
lean_inc(x_627);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_628 = x_37;
} else {
 lean_dec_ref(x_37);
 x_628 = lean_box(0);
}
x_629 = lean_ctor_get(x_38, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_630 = x_38;
} else {
 lean_dec_ref(x_38);
 x_630 = lean_box(0);
}
x_631 = lean_ctor_get(x_39, 0);
x_632 = lean_ctor_get(x_39, 1);
x_633 = lean_ctor_get(x_39, 2);
x_634 = lean_nat_dec_lt(x_632, x_633);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
if (lean_is_scalar(x_630)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_630;
}
lean_ctor_set(x_635, 0, x_39);
lean_ctor_set(x_635, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_628;
}
lean_ctor_set(x_636, 0, x_627);
lean_ctor_set(x_636, 1, x_635);
if (lean_is_scalar(x_626)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_626;
}
lean_ctor_set(x_637, 0, x_625);
lean_ctor_set(x_637, 1, x_636);
if (lean_is_scalar(x_624)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_624;
}
lean_ctor_set(x_638, 0, x_623);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_622);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_640, 0, x_639);
x_641 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_641, 0, x_640);
x_13 = x_641;
goto block_32;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
lean_inc(x_633);
lean_inc(x_632);
lean_inc_ref(x_631);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_642 = x_39;
} else {
 lean_dec_ref(x_39);
 x_642 = lean_box(0);
}
x_643 = lean_ctor_get(x_627, 0);
x_644 = lean_ctor_get(x_627, 1);
x_645 = lean_ctor_get(x_627, 2);
x_646 = lean_array_fget(x_631, x_632);
x_647 = lean_unsigned_to_nat(1u);
x_648 = lean_nat_add(x_632, x_647);
lean_dec(x_632);
if (lean_is_scalar(x_642)) {
 x_649 = lean_alloc_ctor(0, 3, 0);
} else {
 x_649 = x_642;
}
lean_ctor_set(x_649, 0, x_631);
lean_ctor_set(x_649, 1, x_648);
lean_ctor_set(x_649, 2, x_633);
x_650 = lean_nat_dec_lt(x_644, x_645);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_646);
if (lean_is_scalar(x_630)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_630;
}
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_628;
}
lean_ctor_set(x_652, 0, x_627);
lean_ctor_set(x_652, 1, x_651);
if (lean_is_scalar(x_626)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_626;
}
lean_ctor_set(x_653, 0, x_625);
lean_ctor_set(x_653, 1, x_652);
if (lean_is_scalar(x_624)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_624;
}
lean_ctor_set(x_654, 0, x_623);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_622);
lean_ctor_set(x_655, 1, x_654);
x_656 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_656, 0, x_655);
x_657 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_657, 0, x_656);
x_13 = x_657;
goto block_32;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
lean_inc(x_645);
lean_inc(x_644);
lean_inc_ref(x_643);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 lean_ctor_release(x_627, 2);
 x_658 = x_627;
} else {
 lean_dec_ref(x_627);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_625, 0);
x_660 = lean_ctor_get(x_625, 1);
x_661 = lean_ctor_get(x_625, 2);
x_662 = lean_array_fget(x_643, x_644);
x_663 = lean_nat_add(x_644, x_647);
lean_dec(x_644);
if (lean_is_scalar(x_658)) {
 x_664 = lean_alloc_ctor(0, 3, 0);
} else {
 x_664 = x_658;
}
lean_ctor_set(x_664, 0, x_643);
lean_ctor_set(x_664, 1, x_663);
lean_ctor_set(x_664, 2, x_645);
x_665 = lean_nat_dec_lt(x_660, x_661);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_662);
lean_dec(x_646);
if (lean_is_scalar(x_630)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_630;
}
lean_ctor_set(x_666, 0, x_649);
lean_ctor_set(x_666, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_628;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_666);
if (lean_is_scalar(x_626)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_626;
}
lean_ctor_set(x_668, 0, x_625);
lean_ctor_set(x_668, 1, x_667);
if (lean_is_scalar(x_624)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_624;
}
lean_ctor_set(x_669, 0, x_623);
lean_ctor_set(x_669, 1, x_668);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_622);
lean_ctor_set(x_670, 1, x_669);
x_671 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_671, 0, x_670);
x_672 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_672, 0, x_671);
x_13 = x_672;
goto block_32;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; 
lean_inc(x_661);
lean_inc(x_660);
lean_inc_ref(x_659);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 lean_ctor_release(x_625, 2);
 x_673 = x_625;
} else {
 lean_dec_ref(x_625);
 x_673 = lean_box(0);
}
x_674 = lean_ctor_get(x_623, 0);
x_675 = lean_ctor_get(x_623, 1);
x_676 = lean_ctor_get(x_623, 2);
x_677 = lean_array_fget(x_659, x_660);
x_678 = lean_nat_add(x_660, x_647);
lean_dec(x_660);
if (lean_is_scalar(x_673)) {
 x_679 = lean_alloc_ctor(0, 3, 0);
} else {
 x_679 = x_673;
}
lean_ctor_set(x_679, 0, x_659);
lean_ctor_set(x_679, 1, x_678);
lean_ctor_set(x_679, 2, x_661);
x_680 = lean_nat_dec_lt(x_675, x_676);
if (x_680 == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_677);
lean_dec(x_662);
lean_dec(x_646);
if (lean_is_scalar(x_630)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_630;
}
lean_ctor_set(x_681, 0, x_649);
lean_ctor_set(x_681, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_628;
}
lean_ctor_set(x_682, 0, x_664);
lean_ctor_set(x_682, 1, x_681);
if (lean_is_scalar(x_626)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_626;
}
lean_ctor_set(x_683, 0, x_679);
lean_ctor_set(x_683, 1, x_682);
if (lean_is_scalar(x_624)) {
 x_684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_684 = x_624;
}
lean_ctor_set(x_684, 0, x_623);
lean_ctor_set(x_684, 1, x_683);
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_622);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_686, 0, x_685);
x_687 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_687, 0, x_686);
x_13 = x_687;
goto block_32;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_inc(x_676);
lean_inc(x_675);
lean_inc_ref(x_674);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 lean_ctor_release(x_623, 2);
 x_688 = x_623;
} else {
 lean_dec_ref(x_623);
 x_688 = lean_box(0);
}
x_689 = lean_ctor_get(x_622, 0);
x_690 = lean_ctor_get(x_622, 1);
x_691 = lean_ctor_get(x_622, 2);
x_692 = lean_array_fget(x_674, x_675);
x_693 = lean_nat_add(x_675, x_647);
lean_dec(x_675);
if (lean_is_scalar(x_688)) {
 x_694 = lean_alloc_ctor(0, 3, 0);
} else {
 x_694 = x_688;
}
lean_ctor_set(x_694, 0, x_674);
lean_ctor_set(x_694, 1, x_693);
lean_ctor_set(x_694, 2, x_676);
x_695 = lean_nat_dec_lt(x_690, x_691);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_692);
lean_dec(x_677);
lean_dec(x_662);
lean_dec(x_646);
if (lean_is_scalar(x_630)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_630;
}
lean_ctor_set(x_696, 0, x_649);
lean_ctor_set(x_696, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_628;
}
lean_ctor_set(x_697, 0, x_664);
lean_ctor_set(x_697, 1, x_696);
if (lean_is_scalar(x_626)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_626;
}
lean_ctor_set(x_698, 0, x_679);
lean_ctor_set(x_698, 1, x_697);
if (lean_is_scalar(x_624)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_624;
}
lean_ctor_set(x_699, 0, x_694);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_622);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_701, 0, x_700);
x_702 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_702, 0, x_701);
x_13 = x_702;
goto block_32;
}
else
{
lean_object* x_703; lean_object* x_704; uint8_t x_705; lean_object* x_706; uint8_t x_707; 
lean_inc(x_691);
lean_inc(x_690);
lean_inc_ref(x_689);
lean_dec(x_630);
lean_dec(x_628);
lean_dec(x_626);
lean_dec(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 lean_ctor_release(x_622, 2);
 x_703 = x_622;
} else {
 lean_dec_ref(x_622);
 x_703 = lean_box(0);
}
x_704 = lean_ctor_get(x_692, 1);
x_705 = lean_ctor_get_uint8(x_692, sizeof(void*)*2);
x_706 = lean_unsigned_to_nat(0u);
x_707 = lean_nat_dec_eq(x_704, x_706);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_703);
lean_dec_ref(x_694);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec_ref(x_689);
lean_dec_ref(x_679);
lean_dec(x_677);
lean_dec_ref(x_664);
lean_dec(x_662);
lean_dec_ref(x_649);
lean_dec(x_646);
lean_dec(x_629);
x_708 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9;
x_709 = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(x_709, 0, x_708);
x_13 = x_709;
goto block_32;
}
else
{
uint8_t x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_710 = 0;
x_711 = lean_array_fget_borrowed(x_689, x_690);
x_712 = lean_box(x_710);
x_713 = lean_box(x_3);
x_714 = lean_box(x_705);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_711);
lean_inc(x_6);
lean_inc_ref(x_2);
x_715 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(x_715, 0, x_677);
lean_closure_set(x_715, 1, x_646);
lean_closure_set(x_715, 2, x_2);
lean_closure_set(x_715, 3, x_6);
lean_closure_set(x_715, 4, x_712);
lean_closure_set(x_715, 5, x_713);
lean_closure_set(x_715, 6, x_711);
lean_closure_set(x_715, 7, x_4);
lean_closure_set(x_715, 8, x_5);
lean_closure_set(x_715, 9, x_714);
lean_closure_set(x_715, 10, x_647);
x_716 = lean_nat_add(x_690, x_647);
lean_dec(x_690);
if (lean_is_scalar(x_703)) {
 x_717 = lean_alloc_ctor(0, 3, 0);
} else {
 x_717 = x_703;
}
lean_ctor_set(x_717, 0, x_689);
lean_ctor_set(x_717, 1, x_716);
lean_ctor_set(x_717, 2, x_691);
x_718 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(x_718, 0, x_662);
lean_closure_set(x_718, 1, x_692);
lean_closure_set(x_718, 2, x_715);
lean_closure_set(x_718, 3, x_629);
lean_closure_set(x_718, 4, x_649);
lean_closure_set(x_718, 5, x_664);
lean_closure_set(x_718, 6, x_679);
lean_closure_set(x_718, 7, x_694);
lean_closure_set(x_718, 8, x_717);
x_13 = x_718;
goto block_32;
}
}
}
}
}
}
}
}
block_32:
{
lean_object* x_14; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_14 = lean_apply_5(x_13, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_6 = x_20;
x_7 = x_18;
goto _start;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_6, x_26);
lean_dec(x_6);
x_6 = x_27;
x_7 = x_25;
goto _start;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_25 = x_5;
} else {
 lean_dec_ref(x_5);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_30 = x_21;
} else {
 lean_dec_ref(x_21);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
x_33 = lean_ctor_get(x_22, 2);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_27;
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_23)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_23;
}
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_25)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_25;
}
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_ctor_get(x_22, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_22, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_22, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
x_46 = lean_ctor_get(x_24, 2);
x_47 = lean_array_fget(x_31, x_32);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_32, x_48);
lean_dec(x_32);
lean_ctor_set(x_22, 1, x_49);
x_50 = lean_nat_dec_lt(x_45, x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_30)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_30;
}
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_27;
}
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_23)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_23;
}
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_25)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_25;
}
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
uint8_t x_56; 
lean_inc(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
x_56 = !lean_is_exclusive(x_24);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_24, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_24, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_24, 0);
lean_dec(x_59);
x_60 = lean_array_fget(x_44, x_45);
x_61 = lean_nat_add(x_45, x_48);
lean_dec(x_45);
lean_ctor_set(x_24, 1, x_61);
if (x_1 == 0)
{
lean_dec(x_60);
goto block_69;
}
else
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
x_70 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_70);
x_71 = l_Lean_Meta_isProof(x_70, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_74 = l_Lean_Meta_mkEqHEq(x_60, x_70, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_75);
x_76 = l_Lean_mkArrow(x_75, x_29, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Expr_isHEq(x_75);
lean_dec(x_75);
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_array_push(x_26, x_80);
x_82 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0));
x_83 = lean_array_push(x_28, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_22);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_24);
lean_ctor_set(x_87, 1, x_86);
x_11 = x_87;
x_12 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_88; 
lean_dec(x_75);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
lean_dec(x_76);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_91 = !lean_is_exclusive(x_74);
if (x_91 == 0)
{
return x_74;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_74, 0);
lean_inc(x_92);
lean_dec(x_74);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_70);
lean_dec(x_60);
x_94 = lean_box(0);
x_95 = lean_array_push(x_26, x_94);
x_96 = lean_array_push(x_28, x_47);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_29);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_22);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_24);
lean_ctor_set(x_100, 1, x_99);
x_11 = x_100;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
uint8_t x_101; 
lean_dec(x_70);
lean_dec_ref(x_24);
lean_dec(x_60);
lean_dec_ref(x_22);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_101 = !lean_is_exclusive(x_71);
if (x_101 == 0)
{
return x_71;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_71, 0);
lean_inc(x_102);
lean_dec(x_71);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
lean_dec(x_60);
goto block_69;
}
}
block_69:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_box(0);
x_63 = lean_array_push(x_26, x_62);
x_64 = lean_array_push(x_28, x_47);
if (lean_is_scalar(x_30)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_30;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_27;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_23)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_23;
}
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_25)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_25;
}
lean_ctor_set(x_68, 0, x_24);
lean_ctor_set(x_68, 1, x_67);
x_11 = x_68;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_24);
x_104 = lean_array_fget(x_44, x_45);
x_105 = lean_nat_add(x_45, x_48);
lean_dec(x_45);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_44);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_46);
if (x_1 == 0)
{
lean_dec(x_104);
goto block_114;
}
else
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
x_115 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_115);
x_116 = l_Lean_Meta_isProof(x_115, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_119 = l_Lean_Meta_mkEqHEq(x_104, x_115, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_120);
x_121 = l_Lean_mkArrow(x_120, x_29, x_8, x_9);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Lean_Expr_isHEq(x_120);
lean_dec(x_120);
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_array_push(x_26, x_125);
x_127 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0));
x_128 = lean_array_push(x_28, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_122);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_22);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_106);
lean_ctor_set(x_132, 1, x_131);
x_11 = x_132;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_120);
lean_dec_ref(x_106);
lean_dec_ref(x_22);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_133 = lean_ctor_get(x_121, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_106);
lean_dec_ref(x_22);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_136 = lean_ctor_get(x_119, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_137 = x_119;
} else {
 lean_dec_ref(x_119);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_115);
lean_dec(x_104);
x_139 = lean_box(0);
x_140 = lean_array_push(x_26, x_139);
x_141 = lean_array_push(x_28, x_47);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_29);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_22);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_106);
lean_ctor_set(x_145, 1, x_144);
x_11 = x_145;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_115);
lean_dec_ref(x_106);
lean_dec(x_104);
lean_dec_ref(x_22);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_146 = lean_ctor_get(x_116, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_147 = x_116;
} else {
 lean_dec_ref(x_116);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_dec(x_104);
goto block_114;
}
}
block_114:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_box(0);
x_108 = lean_array_push(x_26, x_107);
x_109 = lean_array_push(x_28, x_47);
if (lean_is_scalar(x_30)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_30;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_27;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_23)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_23;
}
lean_ctor_set(x_112, 0, x_22);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_25)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_25;
}
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
x_11 = x_113;
x_12 = lean_box(0);
goto block_16;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_22);
x_149 = lean_ctor_get(x_24, 0);
x_150 = lean_ctor_get(x_24, 1);
x_151 = lean_ctor_get(x_24, 2);
x_152 = lean_array_fget(x_31, x_32);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_add(x_32, x_153);
lean_dec(x_32);
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_31);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_33);
x_156 = lean_nat_dec_lt(x_150, x_151);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_152);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_30)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_30;
}
lean_ctor_set(x_157, 0, x_28);
lean_ctor_set(x_157, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_27;
}
lean_ctor_set(x_158, 0, x_26);
lean_ctor_set(x_158, 1, x_157);
if (lean_is_scalar(x_23)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_23;
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_25)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_25;
}
lean_ctor_set(x_160, 0, x_24);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_inc(x_151);
lean_inc(x_150);
lean_inc_ref(x_149);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_162 = x_24;
} else {
 lean_dec_ref(x_24);
 x_162 = lean_box(0);
}
x_163 = lean_array_fget(x_149, x_150);
x_164 = lean_nat_add(x_150, x_153);
lean_dec(x_150);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 3, 0);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_151);
if (x_1 == 0)
{
lean_dec(x_163);
goto block_173;
}
else
{
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
x_174 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_174);
x_175 = l_Lean_Meta_isProof(x_174, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_178 = l_Lean_Meta_mkEqHEq(x_163, x_174, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_179);
x_180 = l_Lean_mkArrow(x_179, x_29, x_8, x_9);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = l_Lean_Expr_isHEq(x_179);
lean_dec(x_179);
x_183 = lean_box(x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_array_push(x_26, x_184);
x_186 = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___closed__0));
x_187 = lean_array_push(x_28, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_155);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_165);
lean_ctor_set(x_191, 1, x_190);
x_11 = x_191;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_179);
lean_dec_ref(x_165);
lean_dec_ref(x_155);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_192 = lean_ctor_get(x_180, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_165);
lean_dec_ref(x_155);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_195 = lean_ctor_get(x_178, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_196 = x_178;
} else {
 lean_dec_ref(x_178);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_174);
lean_dec(x_163);
x_198 = lean_box(0);
x_199 = lean_array_push(x_26, x_198);
x_200 = lean_array_push(x_28, x_152);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_29);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_155);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_165);
lean_ctor_set(x_204, 1, x_203);
x_11 = x_204;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_174);
lean_dec_ref(x_165);
lean_dec(x_163);
lean_dec_ref(x_155);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_205 = lean_ctor_get(x_175, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_206 = x_175;
} else {
 lean_dec_ref(x_175);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_dec(x_163);
goto block_173;
}
}
block_173:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_box(0);
x_167 = lean_array_push(x_26, x_166);
x_168 = lean_array_push(x_28, x_152);
if (lean_is_scalar(x_30)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_30;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_27;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
if (lean_is_scalar(x_23)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_23;
}
lean_ctor_set(x_171, 0, x_155);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_25)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_25;
}
lean_ctor_set(x_172, 0, x_165);
lean_ctor_set(x_172, 1, x_171);
x_11 = x_172;
x_12 = lean_box(0);
goto block_16;
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_array_get_size(x_7);
x_131 = lean_array_get_size(x_6);
x_132 = lean_nat_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_133 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_134 = l_Nat_reprFast(x_131);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lean_MessageData_ofFormat(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_139, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
x_14 = lean_box(0);
goto block_129;
}
block_129:
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
x_15 = lean_apply_7(x_1, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
x_20 = lean_array_get_size(x_3);
x_21 = l_Array_toSubarray___redArg(x_3, x_18, x_20);
x_22 = lean_array_get_size(x_17);
x_23 = l_Array_toSubarray___redArg(x_17, x_18, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_size(x_7);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(x_4, x_7, x_28, x_5, x_27, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = 0;
x_42 = 1;
x_43 = 1;
lean_inc(x_40);
x_44 = l_Lean_Meta_mkLambdaFVars(x_7, x_40, x_41, x_42, x_41, x_42, x_43, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_Meta_getLevel(x_40, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_36, 1, x_39);
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set(x_33, 0, x_48);
lean_ctor_set(x_31, 0, x_45);
lean_ctor_set(x_46, 0, x_31);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_36, 1, x_39);
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set(x_33, 0, x_49);
lean_ctor_set(x_31, 0, x_45);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_31);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_45);
lean_free_object(x_36);
lean_dec(x_39);
lean_free_object(x_33);
lean_dec(x_38);
lean_free_object(x_31);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_33);
lean_dec(x_38);
lean_free_object(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
return x_44;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_36, 0);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_36);
x_60 = 0;
x_61 = 1;
x_62 = 1;
lean_inc(x_59);
x_63 = l_Lean_Meta_mkLambdaFVars(x_7, x_59, x_60, x_61, x_60, x_61, x_62, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_getLevel(x_59, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_33, 1, x_68);
lean_ctor_set(x_33, 0, x_66);
lean_ctor_set(x_31, 0, x_64);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_31);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_58);
lean_free_object(x_33);
lean_dec(x_57);
lean_free_object(x_31);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_33);
lean_dec(x_57);
lean_free_object(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_33, 1);
x_77 = lean_ctor_get(x_33, 0);
lean_inc(x_76);
lean_inc(x_77);
lean_dec(x_33);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = 0;
x_82 = 1;
x_83 = 1;
lean_inc(x_79);
x_84 = l_Lean_Meta_mkLambdaFVars(x_7, x_79, x_81, x_82, x_81, x_82, x_83, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Meta_getLevel(x_79, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_78);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_31, 1, x_90);
lean_ctor_set(x_31, 0, x_85);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_31);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_free_object(x_31);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_free_object(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_31, 1);
lean_inc(x_98);
lean_dec(x_31);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
x_105 = 0;
x_106 = 1;
x_107 = 1;
lean_inc(x_103);
x_108 = l_Lean_Meta_mkLambdaFVars(x_7, x_103, x_105, x_106, x_105, x_106, x_107, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l_Lean_Meta_getLevel(x_103, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_104;
}
lean_ctor_set(x_113, 0, x_100);
lean_ctor_set(x_113, 1, x_102);
if (lean_is_scalar(x_101)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_101;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
x_117 = lean_ctor_get(x_110, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_120 = lean_ctor_get(x_108, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_121 = x_108;
} else {
 lean_dec_ref(x_108);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_123 = !lean_is_exclusive(x_29);
if (x_123 == 0)
{
return x_29;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_29, 0);
lean_inc(x_124);
lean_dec(x_29);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_126 = !lean_is_exclusive(x_15);
if (x_126 == 0)
{
return x_15;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_15, 0);
lean_inc(x_127);
lean_dec(x_15);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
x_26 = lean_ctor_get(x_19, 2);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_inc(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_19, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_19, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
x_35 = lean_array_fget(x_24, x_25);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_25, x_36);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_37);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_23);
lean_dec(x_20);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_22);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
x_10 = x_49;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_35, 0);
lean_inc(x_50);
lean_dec_ref(x_35);
x_51 = lean_array_uget(x_1, x_3);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_53 = l_Lean_Meta_mkEqRefl(x_51, x_5, x_6, x_7, x_8);
x_38 = x_53;
goto block_47;
}
else
{
lean_object* x_54; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_54 = l_Lean_Meta_mkHEqRefl(x_51, x_5, x_6, x_7, x_8);
x_38 = x_54;
goto block_47;
}
}
block_47:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_array_push(x_22, x_39);
x_41 = lean_nat_add(x_21, x_36);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_23;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
if (lean_is_scalar(x_20)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_20;
}
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_42);
x_10 = x_43;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_19);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_19);
x_55 = lean_array_fget(x_24, x_25);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_25, x_56);
lean_dec(x_25);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_24);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_26);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_23);
lean_dec(x_20);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_21);
lean_ctor_set(x_69, 1, x_22);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_69);
x_10 = x_70;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
lean_dec_ref(x_55);
x_72 = lean_array_uget(x_1, x_3);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_74 = l_Lean_Meta_mkEqRefl(x_72, x_5, x_6, x_7, x_8);
x_59 = x_74;
goto block_68;
}
else
{
lean_object* x_75; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_75 = l_Lean_Meta_mkHEqRefl(x_72, x_5, x_6, x_7, x_8);
x_59 = x_75;
goto block_68;
}
}
block_68:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_array_push(x_22, x_60);
x_62 = lean_nat_add(x_21, x_56);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_23;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
if (lean_is_scalar(x_20)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_20;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_10 = x_64;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_58);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc_ref(x_4);
x_12 = l_Lean_FVarId_getUserName___redArg(x_11, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(x_8, x_9, x_1, x_3, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_1, x_2, x_3, x_4, x_4, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_push(x_5, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_array_push(x_5, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = l_Lean_Meta_instantiateLambda(x_1, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_16 = lean_apply_9(x_3, x_4, x_5, x_2, x_15, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Array_append___redArg(x_2, x_6);
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_18, x_17, x_7, x_8, x_7, x_8, x_19, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_18);
return x_20;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_16;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_7);
x_15 = lean_unbox(x_8);
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_box(x_3);
x_18 = lean_box(x_7);
lean_inc_ref(x_4);
x_19 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 13, 8);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_6);
lean_closure_set(x_19, 4, x_9);
lean_closure_set(x_19, 5, x_8);
lean_closure_set(x_19, 6, x_17);
lean_closure_set(x_19, 7, x_18);
x_20 = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(x_4, x_16, x_19, x_10, x_11, x_12, x_13);
lean_dec(x_16);
lean_dec_ref(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_7);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(x_1, x_2, x_15, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_3);
x_16 = lean_box(x_6);
x_17 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(x_9, x_18, x_17, x_3, x_3, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_31; 
x_31 = lean_nat_dec_lt(x_4, x_1);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_34, 1);
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
x_47 = lean_ctor_get(x_35, 2);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_5);
x_50 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_50, 0, x_49);
x_11 = x_50;
goto block_30;
}
else
{
uint8_t x_51; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_ctor_get(x_35, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_35, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_35, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_40, 0);
x_56 = lean_ctor_get(x_40, 1);
x_57 = lean_ctor_get(x_40, 2);
x_58 = lean_array_fget(x_45, x_46);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_46, x_59);
lean_dec(x_46);
lean_ctor_set(x_35, 1, x_60);
x_61 = lean_nat_dec_lt(x_56, x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_5);
x_63 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_63, 0, x_62);
x_11 = x_63;
goto block_30;
}
else
{
uint8_t x_64; 
lean_inc(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
x_64 = !lean_is_exclusive(x_40);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_40, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_40, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_40, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 0);
x_69 = lean_ctor_get(x_37, 1);
x_70 = lean_ctor_get(x_37, 2);
x_71 = lean_array_fget(x_55, x_56);
x_72 = lean_nat_add(x_56, x_59);
lean_dec(x_56);
lean_ctor_set(x_40, 1, x_72);
x_73 = lean_nat_dec_lt(x_69, x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_58);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_5);
x_75 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_75, 0, x_74);
x_11 = x_75;
goto block_30;
}
else
{
uint8_t x_76; 
lean_inc(x_70);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_5);
x_76 = !lean_is_exclusive(x_37);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_37, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_37, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_37, 0);
lean_dec(x_79);
x_80 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_81 = 0;
x_82 = lean_array_fget_borrowed(x_68, x_69);
x_83 = lean_box(x_81);
x_84 = lean_box(x_73);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_82);
x_85 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_85, 0, x_82);
lean_closure_set(x_85, 1, x_80);
lean_closure_set(x_85, 2, x_83);
lean_closure_set(x_85, 3, x_2);
lean_closure_set(x_85, 4, x_4);
lean_closure_set(x_85, 5, x_84);
lean_closure_set(x_85, 6, x_3);
x_86 = lean_nat_add(x_69, x_59);
lean_dec(x_69);
lean_ctor_set(x_37, 1, x_86);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_71);
x_88 = lean_box(x_81);
x_89 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_89, 0, x_58);
lean_closure_set(x_89, 1, x_87);
lean_closure_set(x_89, 2, x_85);
lean_closure_set(x_89, 3, x_88);
lean_closure_set(x_89, 4, x_43);
lean_closure_set(x_89, 5, x_35);
lean_closure_set(x_89, 6, x_40);
lean_closure_set(x_89, 7, x_37);
x_11 = x_89;
goto block_30;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_37);
x_90 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_91 = 0;
x_92 = lean_array_fget_borrowed(x_68, x_69);
x_93 = lean_box(x_91);
x_94 = lean_box(x_73);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_92);
x_95 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_95, 0, x_92);
lean_closure_set(x_95, 1, x_90);
lean_closure_set(x_95, 2, x_93);
lean_closure_set(x_95, 3, x_2);
lean_closure_set(x_95, 4, x_4);
lean_closure_set(x_95, 5, x_94);
lean_closure_set(x_95, 6, x_3);
x_96 = lean_nat_add(x_69, x_59);
lean_dec(x_69);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_68);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_70);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_71);
x_99 = lean_box(x_91);
x_100 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_100, 0, x_58);
lean_closure_set(x_100, 1, x_98);
lean_closure_set(x_100, 2, x_95);
lean_closure_set(x_100, 3, x_99);
lean_closure_set(x_100, 4, x_43);
lean_closure_set(x_100, 5, x_35);
lean_closure_set(x_100, 6, x_40);
lean_closure_set(x_100, 7, x_97);
x_11 = x_100;
goto block_30;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_40);
x_101 = lean_ctor_get(x_37, 0);
x_102 = lean_ctor_get(x_37, 1);
x_103 = lean_ctor_get(x_37, 2);
x_104 = lean_array_fget(x_55, x_56);
x_105 = lean_nat_add(x_56, x_59);
lean_dec(x_56);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_55);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_57);
x_107 = lean_nat_dec_lt(x_102, x_103);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
lean_dec(x_58);
lean_ctor_set(x_33, 0, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_5);
x_109 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_109, 0, x_108);
x_11 = x_109;
goto block_30;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_5);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_110 = x_37;
} else {
 lean_dec_ref(x_37);
 x_110 = lean_box(0);
}
x_111 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_112 = 0;
x_113 = lean_array_fget_borrowed(x_101, x_102);
x_114 = lean_box(x_112);
x_115 = lean_box(x_107);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_113);
x_116 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_116, 0, x_113);
lean_closure_set(x_116, 1, x_111);
lean_closure_set(x_116, 2, x_114);
lean_closure_set(x_116, 3, x_2);
lean_closure_set(x_116, 4, x_4);
lean_closure_set(x_116, 5, x_115);
lean_closure_set(x_116, 6, x_3);
x_117 = lean_nat_add(x_102, x_59);
lean_dec(x_102);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 3, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_101);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_103);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_104);
x_120 = lean_box(x_112);
x_121 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_121, 0, x_58);
lean_closure_set(x_121, 1, x_119);
lean_closure_set(x_121, 2, x_116);
lean_closure_set(x_121, 3, x_120);
lean_closure_set(x_121, 4, x_43);
lean_closure_set(x_121, 5, x_35);
lean_closure_set(x_121, 6, x_106);
lean_closure_set(x_121, 7, x_118);
x_11 = x_121;
goto block_30;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_35);
x_122 = lean_ctor_get(x_40, 0);
x_123 = lean_ctor_get(x_40, 1);
x_124 = lean_ctor_get(x_40, 2);
x_125 = lean_array_fget(x_45, x_46);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_add(x_46, x_126);
lean_dec(x_46);
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_45);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_47);
x_129 = lean_nat_dec_lt(x_123, x_124);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_ctor_set(x_34, 0, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_5);
x_131 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_131, 0, x_130);
x_11 = x_131;
goto block_30;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_132 = x_40;
} else {
 lean_dec_ref(x_40);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_37, 0);
x_134 = lean_ctor_get(x_37, 1);
x_135 = lean_ctor_get(x_37, 2);
x_136 = lean_array_fget(x_122, x_123);
x_137 = lean_nat_add(x_123, x_126);
lean_dec(x_123);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_124);
x_139 = lean_nat_dec_lt(x_134, x_135);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_136);
lean_dec(x_125);
lean_ctor_set(x_34, 0, x_128);
lean_ctor_set(x_33, 0, x_138);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_5);
x_141 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_141, 0, x_140);
x_11 = x_141;
goto block_30;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_inc(x_135);
lean_inc(x_134);
lean_inc_ref(x_133);
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_5);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_142 = x_37;
} else {
 lean_dec_ref(x_37);
 x_142 = lean_box(0);
}
x_143 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_144 = 0;
x_145 = lean_array_fget_borrowed(x_133, x_134);
x_146 = lean_box(x_144);
x_147 = lean_box(x_139);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_145);
x_148 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_148, 0, x_145);
lean_closure_set(x_148, 1, x_143);
lean_closure_set(x_148, 2, x_146);
lean_closure_set(x_148, 3, x_2);
lean_closure_set(x_148, 4, x_4);
lean_closure_set(x_148, 5, x_147);
lean_closure_set(x_148, 6, x_3);
x_149 = lean_nat_add(x_134, x_126);
lean_dec(x_134);
if (lean_is_scalar(x_142)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_142;
}
lean_ctor_set(x_150, 0, x_133);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_135);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_136);
x_152 = lean_box(x_144);
x_153 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_153, 0, x_125);
lean_closure_set(x_153, 1, x_151);
lean_closure_set(x_153, 2, x_148);
lean_closure_set(x_153, 3, x_152);
lean_closure_set(x_153, 4, x_43);
lean_closure_set(x_153, 5, x_128);
lean_closure_set(x_153, 6, x_138);
lean_closure_set(x_153, 7, x_150);
x_11 = x_153;
goto block_30;
}
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_154 = lean_ctor_get(x_34, 1);
lean_inc(x_154);
lean_dec(x_34);
x_155 = lean_ctor_get(x_35, 0);
x_156 = lean_ctor_get(x_35, 1);
x_157 = lean_ctor_get(x_35, 2);
x_158 = lean_nat_dec_lt(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_154);
lean_ctor_set(x_33, 1, x_159);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_5);
x_161 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_161, 0, x_160);
x_11 = x_161;
goto block_30;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_162 = x_35;
} else {
 lean_dec_ref(x_35);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_40, 0);
x_164 = lean_ctor_get(x_40, 1);
x_165 = lean_ctor_get(x_40, 2);
x_166 = lean_array_fget(x_155, x_156);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_add(x_156, x_167);
lean_dec(x_156);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_155);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_157);
x_170 = lean_nat_dec_lt(x_164, x_165);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_166);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_154);
lean_ctor_set(x_33, 1, x_171);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_5);
x_173 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_173, 0, x_172);
x_11 = x_173;
goto block_30;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_inc(x_165);
lean_inc(x_164);
lean_inc_ref(x_163);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_174 = x_40;
} else {
 lean_dec_ref(x_40);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_37, 0);
x_176 = lean_ctor_get(x_37, 1);
x_177 = lean_ctor_get(x_37, 2);
x_178 = lean_array_fget(x_163, x_164);
x_179 = lean_nat_add(x_164, x_167);
lean_dec(x_164);
if (lean_is_scalar(x_174)) {
 x_180 = lean_alloc_ctor(0, 3, 0);
} else {
 x_180 = x_174;
}
lean_ctor_set(x_180, 0, x_163);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_180, 2, x_165);
x_181 = lean_nat_dec_lt(x_176, x_177);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
lean_dec(x_166);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_169);
lean_ctor_set(x_182, 1, x_154);
lean_ctor_set(x_33, 1, x_182);
lean_ctor_set(x_33, 0, x_180);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_5);
x_184 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_184, 0, x_183);
x_11 = x_184;
goto block_30;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_inc(x_177);
lean_inc(x_176);
lean_inc_ref(x_175);
lean_free_object(x_33);
lean_free_object(x_5);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_185 = x_37;
} else {
 lean_dec_ref(x_37);
 x_185 = lean_box(0);
}
x_186 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_187 = 0;
x_188 = lean_array_fget_borrowed(x_175, x_176);
x_189 = lean_box(x_187);
x_190 = lean_box(x_181);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_188);
x_191 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_191, 0, x_188);
lean_closure_set(x_191, 1, x_186);
lean_closure_set(x_191, 2, x_189);
lean_closure_set(x_191, 3, x_2);
lean_closure_set(x_191, 4, x_4);
lean_closure_set(x_191, 5, x_190);
lean_closure_set(x_191, 6, x_3);
x_192 = lean_nat_add(x_176, x_167);
lean_dec(x_176);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_175);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_177);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_178);
x_195 = lean_box(x_187);
x_196 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_196, 0, x_166);
lean_closure_set(x_196, 1, x_194);
lean_closure_set(x_196, 2, x_191);
lean_closure_set(x_196, 3, x_195);
lean_closure_set(x_196, 4, x_154);
lean_closure_set(x_196, 5, x_169);
lean_closure_set(x_196, 6, x_180);
lean_closure_set(x_196, 7, x_193);
x_11 = x_196;
goto block_30;
}
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_197 = lean_ctor_get(x_33, 0);
lean_inc(x_197);
lean_dec(x_33);
x_198 = lean_ctor_get(x_34, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_199 = x_34;
} else {
 lean_dec_ref(x_34);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_35, 0);
x_201 = lean_ctor_get(x_35, 1);
x_202 = lean_ctor_get(x_35, 2);
x_203 = lean_nat_dec_lt(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
if (lean_is_scalar(x_199)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_199;
}
lean_ctor_set(x_204, 0, x_35);
lean_ctor_set(x_204, 1, x_198);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_197);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_5, 1, x_205);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_5);
x_207 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_207, 0, x_206);
x_11 = x_207;
goto block_30;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_inc(x_202);
lean_inc(x_201);
lean_inc_ref(x_200);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_208 = x_35;
} else {
 lean_dec_ref(x_35);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_197, 0);
x_210 = lean_ctor_get(x_197, 1);
x_211 = lean_ctor_get(x_197, 2);
x_212 = lean_array_fget(x_200, x_201);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_201, x_213);
lean_dec(x_201);
if (lean_is_scalar(x_208)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_208;
}
lean_ctor_set(x_215, 0, x_200);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_202);
x_216 = lean_nat_dec_lt(x_210, x_211);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_212);
if (lean_is_scalar(x_199)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_199;
}
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_198);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_197);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_5, 1, x_218);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_5);
x_220 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_220, 0, x_219);
x_11 = x_220;
goto block_30;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_inc(x_211);
lean_inc(x_210);
lean_inc_ref(x_209);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 x_221 = x_197;
} else {
 lean_dec_ref(x_197);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_37, 0);
x_223 = lean_ctor_get(x_37, 1);
x_224 = lean_ctor_get(x_37, 2);
x_225 = lean_array_fget(x_209, x_210);
x_226 = lean_nat_add(x_210, x_213);
lean_dec(x_210);
if (lean_is_scalar(x_221)) {
 x_227 = lean_alloc_ctor(0, 3, 0);
} else {
 x_227 = x_221;
}
lean_ctor_set(x_227, 0, x_209);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_211);
x_228 = lean_nat_dec_lt(x_223, x_224);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_225);
lean_dec(x_212);
if (lean_is_scalar(x_199)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_199;
}
lean_ctor_set(x_229, 0, x_215);
lean_ctor_set(x_229, 1, x_198);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_5, 1, x_230);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_5);
x_232 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_232, 0, x_231);
x_11 = x_232;
goto block_30;
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_inc(x_224);
lean_inc(x_223);
lean_inc_ref(x_222);
lean_dec(x_199);
lean_free_object(x_5);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_233 = x_37;
} else {
 lean_dec_ref(x_37);
 x_233 = lean_box(0);
}
x_234 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_235 = 0;
x_236 = lean_array_fget_borrowed(x_222, x_223);
x_237 = lean_box(x_235);
x_238 = lean_box(x_228);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_236);
x_239 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_239, 0, x_236);
lean_closure_set(x_239, 1, x_234);
lean_closure_set(x_239, 2, x_237);
lean_closure_set(x_239, 3, x_2);
lean_closure_set(x_239, 4, x_4);
lean_closure_set(x_239, 5, x_238);
lean_closure_set(x_239, 6, x_3);
x_240 = lean_nat_add(x_223, x_213);
lean_dec(x_223);
if (lean_is_scalar(x_233)) {
 x_241 = lean_alloc_ctor(0, 3, 0);
} else {
 x_241 = x_233;
}
lean_ctor_set(x_241, 0, x_222);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_241, 2, x_224);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_225);
x_243 = lean_box(x_235);
x_244 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_244, 0, x_212);
lean_closure_set(x_244, 1, x_242);
lean_closure_set(x_244, 2, x_239);
lean_closure_set(x_244, 3, x_243);
lean_closure_set(x_244, 4, x_198);
lean_closure_set(x_244, 5, x_215);
lean_closure_set(x_244, 6, x_227);
lean_closure_set(x_244, 7, x_241);
x_11 = x_244;
goto block_30;
}
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_245 = lean_ctor_get(x_5, 0);
lean_inc(x_245);
lean_dec(x_5);
x_246 = lean_ctor_get(x_33, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_247 = x_33;
} else {
 lean_dec_ref(x_33);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_34, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_249 = x_34;
} else {
 lean_dec_ref(x_34);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_35, 0);
x_251 = lean_ctor_get(x_35, 1);
x_252 = lean_ctor_get(x_35, 2);
x_253 = lean_nat_dec_lt(x_251, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_35);
lean_ctor_set(x_254, 1, x_248);
if (lean_is_scalar(x_247)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_247;
}
lean_ctor_set(x_255, 0, x_246);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_245);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_258, 0, x_257);
x_11 = x_258;
goto block_30;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_inc(x_252);
lean_inc(x_251);
lean_inc_ref(x_250);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_259 = x_35;
} else {
 lean_dec_ref(x_35);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_246, 0);
x_261 = lean_ctor_get(x_246, 1);
x_262 = lean_ctor_get(x_246, 2);
x_263 = lean_array_fget(x_250, x_251);
x_264 = lean_unsigned_to_nat(1u);
x_265 = lean_nat_add(x_251, x_264);
lean_dec(x_251);
if (lean_is_scalar(x_259)) {
 x_266 = lean_alloc_ctor(0, 3, 0);
} else {
 x_266 = x_259;
}
lean_ctor_set(x_266, 0, x_250);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set(x_266, 2, x_252);
x_267 = lean_nat_dec_lt(x_261, x_262);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_263);
if (lean_is_scalar(x_249)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_249;
}
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_248);
if (lean_is_scalar(x_247)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_247;
}
lean_ctor_set(x_269, 0, x_246);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_245);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_272, 0, x_271);
x_11 = x_272;
goto block_30;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_inc(x_262);
lean_inc(x_261);
lean_inc_ref(x_260);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_273 = x_246;
} else {
 lean_dec_ref(x_246);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_245, 0);
x_275 = lean_ctor_get(x_245, 1);
x_276 = lean_ctor_get(x_245, 2);
x_277 = lean_array_fget(x_260, x_261);
x_278 = lean_nat_add(x_261, x_264);
lean_dec(x_261);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 3, 0);
} else {
 x_279 = x_273;
}
lean_ctor_set(x_279, 0, x_260);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set(x_279, 2, x_262);
x_280 = lean_nat_dec_lt(x_275, x_276);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_277);
lean_dec(x_263);
if (lean_is_scalar(x_249)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_249;
}
lean_ctor_set(x_281, 0, x_266);
lean_ctor_set(x_281, 1, x_248);
if (lean_is_scalar(x_247)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_247;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_245);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_285 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_285, 0, x_284);
x_11 = x_285;
goto block_30;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_inc(x_276);
lean_inc(x_275);
lean_inc_ref(x_274);
lean_dec(x_249);
lean_dec(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 x_286 = x_245;
} else {
 lean_dec_ref(x_245);
 x_286 = lean_box(0);
}
x_287 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
x_288 = 0;
x_289 = lean_array_fget_borrowed(x_274, x_275);
x_290 = lean_box(x_288);
x_291 = lean_box(x_280);
lean_inc(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_289);
x_292 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(x_292, 0, x_289);
lean_closure_set(x_292, 1, x_287);
lean_closure_set(x_292, 2, x_290);
lean_closure_set(x_292, 3, x_2);
lean_closure_set(x_292, 4, x_4);
lean_closure_set(x_292, 5, x_291);
lean_closure_set(x_292, 6, x_3);
x_293 = lean_nat_add(x_275, x_264);
lean_dec(x_275);
if (lean_is_scalar(x_286)) {
 x_294 = lean_alloc_ctor(0, 3, 0);
} else {
 x_294 = x_286;
}
lean_ctor_set(x_294, 0, x_274);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_276);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_277);
x_296 = lean_box(x_288);
x_297 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(x_297, 0, x_263);
lean_closure_set(x_297, 1, x_295);
lean_closure_set(x_297, 2, x_292);
lean_closure_set(x_297, 3, x_296);
lean_closure_set(x_297, 4, x_248);
lean_closure_set(x_297, 5, x_266);
lean_closure_set(x_297, 6, x_279);
lean_closure_set(x_297, 7, x_294);
x_11 = x_297;
goto block_30;
}
}
}
}
}
block_30:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_12 = lean_apply_5(x_11, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_4 = x_18;
x_5 = x_16;
goto _start;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_4, x_3);
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_apply_6(x_1, x_12, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_16, x_3, x_14);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_13 = lean_st_ref_get(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_ctor_get(x_1, 5);
x_21 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_22);
lean_inc(x_16);
x_105 = l_Lean_isCasesOnRecursor(x_14, x_16);
if (x_105 == 0)
{
lean_object* x_596; lean_object* x_597; 
lean_inc(x_16);
x_596 = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(x_16, x_11);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
lean_dec_ref(x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_598 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_599 = l_Lean_MessageData_ofName(x_16);
x_600 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
x_601 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
x_602 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
x_603 = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(x_602, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
return x_603;
}
else
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_606, 0, x_605);
return x_606;
}
}
else
{
lean_object* x_607; lean_object* x_608; 
x_607 = lean_ctor_get(x_597, 0);
lean_inc(x_607);
lean_dec_ref(x_597);
x_608 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_607);
lean_dec(x_607);
x_555 = x_608;
x_556 = x_8;
x_557 = x_9;
x_558 = x_10;
x_559 = x_11;
x_560 = lean_box(0);
goto block_595;
}
}
else
{
lean_object* x_609; 
x_609 = lean_unsigned_to_nat(0u);
x_555 = x_609;
x_556 = x_8;
x_557 = x_9;
x_558 = x_10;
x_559 = x_11;
x_560 = lean_box(0);
goto block_595;
}
block_104:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_27);
x_37 = lean_array_to_list(x_27);
lean_inc(x_16);
x_38 = l_Lean_mkConst(x_16, x_37);
x_39 = l_Lean_mkAppN(x_38, x_28);
lean_inc_ref(x_25);
x_40 = l_Lean_Expr_app___override(x_39, x_25);
x_41 = l_Lean_mkAppN(x_40, x_26);
x_42 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
lean_inc_ref(x_41);
x_43 = l_Lean_indentExpr(x_41);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_45, 0, x_44);
lean_inc_ref(x_41);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_46, 0, x_41);
lean_inc(x_32);
lean_inc_ref(x_30);
lean_inc(x_34);
lean_inc_ref(x_24);
x_47 = l_Lean_Meta_mapErrorImp___redArg(x_46, x_45, x_24, x_34, x_30, x_32);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_47);
x_48 = lean_array_get_size(x_21);
lean_inc(x_32);
lean_inc_ref(x_30);
lean_inc(x_34);
lean_inc_ref(x_24);
x_49 = l_Lean_Meta_inferArgumentTypesN(x_48, x_41, x_24, x_34, x_30, x_32);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_MatcherApp_altNumParams(x_1);
x_52 = lean_array_get_size(x_51);
x_53 = lean_array_get_size(x_50);
lean_inc(x_33);
x_54 = l_Array_toSubarray___redArg(x_21, x_33, x_48);
lean_inc(x_33);
x_55 = l_Array_toSubarray___redArg(x_51, x_33, x_52);
lean_inc(x_33);
x_56 = l_Array_toSubarray___redArg(x_50, x_33, x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_31);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_32);
lean_inc_ref(x_30);
lean_inc(x_34);
lean_inc_ref(x_24);
x_60 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(x_48, x_6, x_23, x_33, x_59, x_24, x_34, x_30, x_32);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_apply_6(x_7, x_22, x_24, x_34, x_30, x_32, lean_box(0));
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_15);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_15, 4);
lean_dec(x_69);
x_70 = l_Array_append___redArg(x_29, x_68);
lean_dec(x_68);
lean_ctor_set(x_15, 4, x_35);
x_71 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_16);
lean_ctor_set(x_71, 2, x_27);
lean_ctor_set(x_71, 3, x_28);
lean_ctor_set(x_71, 4, x_25);
lean_ctor_set(x_71, 5, x_26);
lean_ctor_set(x_71, 6, x_64);
lean_ctor_set(x_71, 7, x_70);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get(x_15, 1);
x_75 = lean_ctor_get(x_15, 2);
x_76 = lean_ctor_get(x_15, 3);
x_77 = lean_ctor_get(x_15, 5);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_15);
x_78 = l_Array_append___redArg(x_29, x_72);
lean_dec(x_72);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_35);
lean_ctor_set(x_79, 5, x_77);
x_80 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_16);
lean_ctor_set(x_80, 2, x_27);
lean_ctor_set(x_80, 3, x_28);
lean_ctor_set(x_80, 4, x_25);
lean_ctor_set(x_80, 5, x_26);
lean_ctor_set(x_80, 6, x_64);
lean_ctor_set(x_80, 7, x_78);
lean_ctor_set(x_65, 0, x_80);
return x_65;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
lean_dec(x_65);
x_82 = lean_ctor_get(x_15, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_15, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_15, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_15, 5);
lean_inc_ref(x_86);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_87 = x_15;
} else {
 lean_dec_ref(x_15);
 x_87 = lean_box(0);
}
x_88 = l_Array_append___redArg(x_29, x_81);
lean_dec(x_81);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_83);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_35);
lean_ctor_set(x_89, 5, x_86);
x_90 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_16);
lean_ctor_set(x_90, 2, x_27);
lean_ctor_set(x_90, 3, x_28);
lean_ctor_set(x_90, 4, x_25);
lean_ctor_set(x_90, 5, x_26);
lean_ctor_set(x_90, 6, x_64);
lean_ctor_set(x_90, 7, x_88);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_64);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
x_92 = !lean_is_exclusive(x_65);
if (x_92 == 0)
{
return x_65;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_65, 0);
lean_inc(x_93);
lean_dec(x_65);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
x_95 = !lean_is_exclusive(x_60);
if (x_95 == 0)
{
return x_60;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_60, 0);
lean_inc(x_96);
lean_dec(x_60);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_49);
if (x_98 == 0)
{
return x_49;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_49, 0);
lean_inc(x_99);
lean_dec(x_49);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_41);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_47);
if (x_101 == 0)
{
return x_47;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_47, 0);
lean_inc(x_102);
lean_dec(x_47);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
block_554:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; size_t x_127; lean_object* x_128; 
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0;
x_121 = l_Array_reverse___redArg(x_108);
x_122 = lean_array_get_size(x_121);
x_123 = l_Array_toSubarray___redArg(x_121, x_119, x_122);
lean_inc_ref(x_110);
x_124 = l_Array_reverse___redArg(x_110);
x_125 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_array_size(x_124);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_128 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(x_124, x_127, x_106, x_126, x_114, x_115, x_116, x_117);
lean_dec_ref(x_124);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
if (x_2 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_free_object(x_129);
lean_dec(x_107);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_23 = x_133;
x_24 = x_114;
x_25 = x_109;
x_26 = x_110;
x_27 = x_113;
x_28 = x_111;
x_29 = x_134;
x_30 = x_116;
x_31 = x_120;
x_32 = x_117;
x_33 = x_119;
x_34 = x_115;
x_35 = x_112;
x_36 = lean_box(0);
goto block_104;
}
else
{
if (x_105 == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_1);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_ctor_get(x_1, 7);
lean_dec(x_136);
x_137 = lean_ctor_get(x_1, 6);
lean_dec(x_137);
x_138 = lean_ctor_get(x_1, 5);
lean_dec(x_138);
x_139 = lean_ctor_get(x_1, 4);
lean_dec(x_139);
x_140 = lean_ctor_get(x_1, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_1, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_1, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
lean_inc_ref(x_113);
x_147 = lean_array_to_list(x_113);
lean_inc(x_147);
lean_inc(x_16);
x_148 = l_Lean_mkConst(x_16, x_147);
x_149 = l_Lean_mkAppN(x_148, x_111);
lean_inc_ref(x_109);
x_150 = l_Lean_Expr_app___override(x_149, x_109);
x_151 = l_Lean_mkAppN(x_150, x_110);
x_152 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
lean_inc_ref(x_151);
x_153 = l_Lean_indentExpr(x_151);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_157, 0, x_156);
lean_inc_ref(x_151);
x_158 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_158, 0, x_151);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_159 = l_Lean_Meta_mapErrorImp___redArg(x_158, x_157, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_159);
x_160 = lean_array_get_size(x_21);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_161 = l_Lean_Meta_inferArgumentTypesN(x_160, x_151, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_163 = lean_get_match_equations_for(x_16, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 2);
lean_inc_ref(x_166);
lean_dec(x_164);
lean_inc(x_165);
x_167 = l_Lean_mkConst(x_165, x_147);
x_168 = l_Lean_mkAppN(x_167, x_111);
lean_inc_ref(x_109);
x_169 = l_Lean_Expr_app___override(x_168, x_109);
x_170 = l_Lean_mkAppN(x_169, x_110);
x_171 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
lean_inc_ref(x_170);
x_172 = l_Lean_indentExpr(x_170);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_155);
x_175 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_175, 0, x_174);
lean_inc_ref(x_170);
x_176 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_176, 0, x_170);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_177 = l_Lean_Meta_mapErrorImp___redArg(x_176, x_175, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
lean_dec_ref(x_177);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_178 = l_Lean_Meta_inferArgumentTypesN(x_160, x_170, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = lean_ctor_get(x_15, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_15, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_15, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_15, 5);
lean_inc_ref(x_184);
lean_dec_ref(x_15);
x_185 = !lean_is_exclusive(x_166);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_186 = lean_ctor_get(x_166, 2);
x_187 = lean_ctor_get(x_166, 5);
lean_dec(x_187);
x_188 = lean_ctor_get(x_166, 4);
lean_dec(x_188);
x_189 = lean_ctor_get(x_166, 3);
lean_dec(x_189);
x_190 = lean_ctor_get(x_166, 1);
lean_dec(x_190);
x_191 = lean_ctor_get(x_166, 0);
lean_dec(x_191);
x_192 = lean_array_get_size(x_182);
x_193 = lean_array_get_size(x_186);
x_194 = lean_array_get_size(x_162);
x_195 = lean_array_get_size(x_179);
x_196 = l_Array_toSubarray___redArg(x_21, x_119, x_160);
lean_inc_ref(x_182);
x_197 = l_Array_toSubarray___redArg(x_182, x_119, x_192);
x_198 = l_Array_toSubarray___redArg(x_186, x_119, x_193);
x_199 = l_Array_toSubarray___redArg(x_162, x_119, x_194);
x_200 = l_Array_toSubarray___redArg(x_179, x_119, x_195);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set(x_131, 0, x_200);
lean_ctor_set(x_129, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_129);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_202);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_204 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_160, x_6, x_2, x_145, x_107, x_119, x_203, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_apply_6(x_7, x_22, x_114, x_115, x_116, x_117, lean_box(0));
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = l_Array_append___redArg(x_146, x_213);
lean_dec(x_213);
lean_ctor_set(x_166, 5, x_184);
lean_ctor_set(x_166, 4, x_112);
lean_ctor_set(x_166, 3, x_183);
lean_ctor_set(x_166, 2, x_182);
lean_ctor_set(x_166, 1, x_181);
lean_ctor_set(x_166, 0, x_180);
lean_ctor_set(x_1, 7, x_214);
lean_ctor_set(x_1, 6, x_210);
lean_ctor_set(x_1, 5, x_110);
lean_ctor_set(x_1, 4, x_109);
lean_ctor_set(x_1, 3, x_111);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_165);
lean_ctor_set(x_1, 0, x_166);
lean_ctor_set(x_211, 0, x_1);
return x_211;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_211, 0);
lean_inc(x_215);
lean_dec(x_211);
x_216 = l_Array_append___redArg(x_146, x_215);
lean_dec(x_215);
lean_ctor_set(x_166, 5, x_184);
lean_ctor_set(x_166, 4, x_112);
lean_ctor_set(x_166, 3, x_183);
lean_ctor_set(x_166, 2, x_182);
lean_ctor_set(x_166, 1, x_181);
lean_ctor_set(x_166, 0, x_180);
lean_ctor_set(x_1, 7, x_216);
lean_ctor_set(x_1, 6, x_210);
lean_ctor_set(x_1, 5, x_110);
lean_ctor_set(x_1, 4, x_109);
lean_ctor_set(x_1, 3, x_111);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_165);
lean_ctor_set(x_1, 0, x_166);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_1);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_dec(x_210);
lean_free_object(x_166);
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_146);
lean_free_object(x_1);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
x_218 = !lean_is_exclusive(x_211);
if (x_218 == 0)
{
return x_211;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_211, 0);
lean_inc(x_219);
lean_dec(x_211);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_free_object(x_166);
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_146);
lean_free_object(x_1);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_22);
lean_dec_ref(x_7);
x_221 = !lean_is_exclusive(x_204);
if (x_221 == 0)
{
return x_204;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_204, 0);
lean_inc(x_222);
lean_dec(x_204);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_224 = lean_ctor_get(x_166, 2);
lean_inc(x_224);
lean_dec(x_166);
x_225 = lean_array_get_size(x_182);
x_226 = lean_array_get_size(x_224);
x_227 = lean_array_get_size(x_162);
x_228 = lean_array_get_size(x_179);
x_229 = l_Array_toSubarray___redArg(x_21, x_119, x_160);
lean_inc_ref(x_182);
x_230 = l_Array_toSubarray___redArg(x_182, x_119, x_225);
x_231 = l_Array_toSubarray___redArg(x_224, x_119, x_226);
x_232 = l_Array_toSubarray___redArg(x_162, x_119, x_227);
x_233 = l_Array_toSubarray___redArg(x_179, x_119, x_228);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set(x_131, 0, x_233);
lean_ctor_set(x_129, 0, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_129);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_230);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_229);
lean_ctor_set(x_236, 1, x_235);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_237 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_160, x_6, x_2, x_145, x_107, x_119, x_236, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_apply_6(x_7, x_22, x_114, x_115, x_116, x_117, lean_box(0));
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = l_Array_append___redArg(x_146, x_245);
lean_dec(x_245);
x_248 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_248, 0, x_180);
lean_ctor_set(x_248, 1, x_181);
lean_ctor_set(x_248, 2, x_182);
lean_ctor_set(x_248, 3, x_183);
lean_ctor_set(x_248, 4, x_112);
lean_ctor_set(x_248, 5, x_184);
lean_ctor_set(x_1, 7, x_247);
lean_ctor_set(x_1, 6, x_243);
lean_ctor_set(x_1, 5, x_110);
lean_ctor_set(x_1, 4, x_109);
lean_ctor_set(x_1, 3, x_111);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_165);
lean_ctor_set(x_1, 0, x_248);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 1, 0);
} else {
 x_249 = x_246;
}
lean_ctor_set(x_249, 0, x_1);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_243);
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_146);
lean_free_object(x_1);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
x_250 = lean_ctor_get(x_244, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_146);
lean_free_object(x_1);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_22);
lean_dec_ref(x_7);
x_253 = lean_ctor_get(x_237, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_254 = x_237;
} else {
 lean_dec_ref(x_237);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_162);
lean_free_object(x_131);
lean_dec(x_146);
lean_dec(x_145);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_256 = !lean_is_exclusive(x_178);
if (x_256 == 0)
{
return x_178;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_178, 0);
lean_inc(x_257);
lean_dec(x_178);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_dec_ref(x_170);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_162);
lean_free_object(x_131);
lean_dec(x_146);
lean_dec(x_145);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_259 = !lean_is_exclusive(x_177);
if (x_259 == 0)
{
return x_177;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_177, 0);
lean_inc(x_260);
lean_dec(x_177);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_162);
lean_dec(x_147);
lean_free_object(x_131);
lean_dec(x_146);
lean_dec(x_145);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_262 = !lean_is_exclusive(x_163);
if (x_262 == 0)
{
return x_163;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_163, 0);
lean_inc(x_263);
lean_dec(x_163);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_147);
lean_free_object(x_131);
lean_dec(x_146);
lean_dec(x_145);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_265 = !lean_is_exclusive(x_161);
if (x_265 == 0)
{
return x_161;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_161, 0);
lean_inc(x_266);
lean_dec(x_161);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec_ref(x_151);
lean_dec(x_147);
lean_free_object(x_131);
lean_dec(x_146);
lean_dec(x_145);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_268 = !lean_is_exclusive(x_159);
if (x_268 == 0)
{
return x_159;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_159, 0);
lean_inc(x_269);
lean_dec(x_159);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_271 = lean_ctor_get(x_131, 0);
x_272 = lean_ctor_get(x_131, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_131);
lean_inc_ref(x_113);
x_273 = lean_array_to_list(x_113);
lean_inc(x_273);
lean_inc(x_16);
x_274 = l_Lean_mkConst(x_16, x_273);
x_275 = l_Lean_mkAppN(x_274, x_111);
lean_inc_ref(x_109);
x_276 = l_Lean_Expr_app___override(x_275, x_109);
x_277 = l_Lean_mkAppN(x_276, x_110);
x_278 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
lean_inc_ref(x_277);
x_279 = l_Lean_indentExpr(x_277);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_283, 0, x_282);
lean_inc_ref(x_277);
x_284 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_284, 0, x_277);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_285 = l_Lean_Meta_mapErrorImp___redArg(x_284, x_283, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec_ref(x_285);
x_286 = lean_array_get_size(x_21);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_287 = l_Lean_Meta_inferArgumentTypesN(x_286, x_277, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_289 = lean_get_match_equations_for(x_16, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 2);
lean_inc_ref(x_292);
lean_dec(x_290);
lean_inc(x_291);
x_293 = l_Lean_mkConst(x_291, x_273);
x_294 = l_Lean_mkAppN(x_293, x_111);
lean_inc_ref(x_109);
x_295 = l_Lean_Expr_app___override(x_294, x_109);
x_296 = l_Lean_mkAppN(x_295, x_110);
x_297 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
lean_inc_ref(x_296);
x_298 = l_Lean_indentExpr(x_296);
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_281);
x_301 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_301, 0, x_300);
lean_inc_ref(x_296);
x_302 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_302, 0, x_296);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_303 = l_Lean_Meta_mapErrorImp___redArg(x_302, x_301, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec_ref(x_303);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_304 = l_Lean_Meta_inferArgumentTypesN(x_286, x_296, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = lean_ctor_get(x_15, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_15, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_308);
x_309 = lean_ctor_get(x_15, 3);
lean_inc(x_309);
x_310 = lean_ctor_get(x_15, 5);
lean_inc_ref(x_310);
lean_dec_ref(x_15);
x_311 = lean_ctor_get(x_292, 2);
lean_inc_ref(x_311);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 lean_ctor_release(x_292, 3);
 lean_ctor_release(x_292, 4);
 lean_ctor_release(x_292, 5);
 x_312 = x_292;
} else {
 lean_dec_ref(x_292);
 x_312 = lean_box(0);
}
x_313 = lean_array_get_size(x_308);
x_314 = lean_array_get_size(x_311);
x_315 = lean_array_get_size(x_288);
x_316 = lean_array_get_size(x_305);
x_317 = l_Array_toSubarray___redArg(x_21, x_119, x_286);
lean_inc_ref(x_308);
x_318 = l_Array_toSubarray___redArg(x_308, x_119, x_313);
x_319 = l_Array_toSubarray___redArg(x_311, x_119, x_314);
x_320 = l_Array_toSubarray___redArg(x_288, x_119, x_315);
x_321 = l_Array_toSubarray___redArg(x_305, x_119, x_316);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_120);
lean_ctor_set(x_129, 1, x_322);
lean_ctor_set(x_129, 0, x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_129);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_318);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_317);
lean_ctor_set(x_325, 1, x_324);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_326 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_286, x_6, x_2, x_271, x_107, x_119, x_325, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec_ref(x_326);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_333 = lean_apply_6(x_7, x_22, x_114, x_115, x_116, x_117, lean_box(0));
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
x_336 = l_Array_append___redArg(x_272, x_334);
lean_dec(x_334);
if (lean_is_scalar(x_312)) {
 x_337 = lean_alloc_ctor(0, 6, 0);
} else {
 x_337 = x_312;
}
lean_ctor_set(x_337, 0, x_306);
lean_ctor_set(x_337, 1, x_307);
lean_ctor_set(x_337, 2, x_308);
lean_ctor_set(x_337, 3, x_309);
lean_ctor_set(x_337, 4, x_112);
lean_ctor_set(x_337, 5, x_310);
lean_ctor_set(x_1, 7, x_336);
lean_ctor_set(x_1, 6, x_332);
lean_ctor_set(x_1, 5, x_110);
lean_ctor_set(x_1, 4, x_109);
lean_ctor_set(x_1, 3, x_111);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_291);
lean_ctor_set(x_1, 0, x_337);
if (lean_is_scalar(x_335)) {
 x_338 = lean_alloc_ctor(0, 1, 0);
} else {
 x_338 = x_335;
}
lean_ctor_set(x_338, 0, x_1);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_332);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
lean_dec_ref(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_291);
lean_dec(x_272);
lean_free_object(x_1);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
x_339 = lean_ctor_get(x_333, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 x_340 = x_333;
} else {
 lean_dec_ref(x_333);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec(x_309);
lean_dec_ref(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_291);
lean_dec(x_272);
lean_free_object(x_1);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_22);
lean_dec_ref(x_7);
x_342 = lean_ctor_get(x_326, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_343 = x_326;
} else {
 lean_dec_ref(x_326);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec_ref(x_292);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_272);
lean_dec(x_271);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_345 = lean_ctor_get(x_304, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_346 = x_304;
} else {
 lean_dec_ref(x_304);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec_ref(x_296);
lean_dec_ref(x_292);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_272);
lean_dec(x_271);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_348 = lean_ctor_get(x_303, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_349 = x_303;
} else {
 lean_dec_ref(x_303);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_288);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_351 = lean_ctor_get(x_289, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_352 = x_289;
} else {
 lean_dec_ref(x_289);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_354 = lean_ctor_get(x_287, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_355 = x_287;
} else {
 lean_dec_ref(x_287);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec_ref(x_277);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_free_object(x_1);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_357 = lean_ctor_get(x_285, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_358 = x_285;
} else {
 lean_dec_ref(x_285);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
return x_359;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_1);
x_360 = lean_ctor_get(x_131, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_131, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_362 = x_131;
} else {
 lean_dec_ref(x_131);
 x_362 = lean_box(0);
}
lean_inc_ref(x_113);
x_363 = lean_array_to_list(x_113);
lean_inc(x_363);
lean_inc(x_16);
x_364 = l_Lean_mkConst(x_16, x_363);
x_365 = l_Lean_mkAppN(x_364, x_111);
lean_inc_ref(x_109);
x_366 = l_Lean_Expr_app___override(x_365, x_109);
x_367 = l_Lean_mkAppN(x_366, x_110);
x_368 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
lean_inc_ref(x_367);
x_369 = l_Lean_indentExpr(x_367);
x_370 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_373, 0, x_372);
lean_inc_ref(x_367);
x_374 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_374, 0, x_367);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_375 = l_Lean_Meta_mapErrorImp___redArg(x_374, x_373, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_375);
x_376 = lean_array_get_size(x_21);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_377 = l_Lean_Meta_inferArgumentTypesN(x_376, x_367, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec_ref(x_377);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_379 = lean_get_match_equations_for(x_16, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 2);
lean_inc_ref(x_382);
lean_dec(x_380);
lean_inc(x_381);
x_383 = l_Lean_mkConst(x_381, x_363);
x_384 = l_Lean_mkAppN(x_383, x_111);
lean_inc_ref(x_109);
x_385 = l_Lean_Expr_app___override(x_384, x_109);
x_386 = l_Lean_mkAppN(x_385, x_110);
x_387 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
lean_inc_ref(x_386);
x_388 = l_Lean_indentExpr(x_386);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_371);
x_391 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_391, 0, x_390);
lean_inc_ref(x_386);
x_392 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_392, 0, x_386);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_393 = l_Lean_Meta_mapErrorImp___redArg(x_392, x_391, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
lean_dec_ref(x_393);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_394 = l_Lean_Meta_inferArgumentTypesN(x_376, x_386, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_396 = lean_ctor_get(x_15, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_15, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_15, 3);
lean_inc(x_399);
x_400 = lean_ctor_get(x_15, 5);
lean_inc_ref(x_400);
lean_dec_ref(x_15);
x_401 = lean_ctor_get(x_382, 2);
lean_inc_ref(x_401);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 lean_ctor_release(x_382, 4);
 lean_ctor_release(x_382, 5);
 x_402 = x_382;
} else {
 lean_dec_ref(x_382);
 x_402 = lean_box(0);
}
x_403 = lean_array_get_size(x_398);
x_404 = lean_array_get_size(x_401);
x_405 = lean_array_get_size(x_378);
x_406 = lean_array_get_size(x_395);
x_407 = l_Array_toSubarray___redArg(x_21, x_119, x_376);
lean_inc_ref(x_398);
x_408 = l_Array_toSubarray___redArg(x_398, x_119, x_403);
x_409 = l_Array_toSubarray___redArg(x_401, x_119, x_404);
x_410 = l_Array_toSubarray___redArg(x_378, x_119, x_405);
x_411 = l_Array_toSubarray___redArg(x_395, x_119, x_406);
if (lean_is_scalar(x_362)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_362;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_120);
lean_ctor_set(x_129, 1, x_412);
lean_ctor_set(x_129, 0, x_410);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_409);
lean_ctor_set(x_413, 1, x_129);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_408);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_407);
lean_ctor_set(x_415, 1, x_414);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_416 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_376, x_6, x_2, x_360, x_107, x_119, x_415, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = lean_apply_6(x_7, x_22, x_114, x_115, x_116, x_117, lean_box(0));
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
x_426 = l_Array_append___redArg(x_361, x_424);
lean_dec(x_424);
if (lean_is_scalar(x_402)) {
 x_427 = lean_alloc_ctor(0, 6, 0);
} else {
 x_427 = x_402;
}
lean_ctor_set(x_427, 0, x_396);
lean_ctor_set(x_427, 1, x_397);
lean_ctor_set(x_427, 2, x_398);
lean_ctor_set(x_427, 3, x_399);
lean_ctor_set(x_427, 4, x_112);
lean_ctor_set(x_427, 5, x_400);
x_428 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_381);
lean_ctor_set(x_428, 2, x_113);
lean_ctor_set(x_428, 3, x_111);
lean_ctor_set(x_428, 4, x_109);
lean_ctor_set(x_428, 5, x_110);
lean_ctor_set(x_428, 6, x_422);
lean_ctor_set(x_428, 7, x_426);
if (lean_is_scalar(x_425)) {
 x_429 = lean_alloc_ctor(0, 1, 0);
} else {
 x_429 = x_425;
}
lean_ctor_set(x_429, 0, x_428);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_422);
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_399);
lean_dec_ref(x_398);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_381);
lean_dec(x_361);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
x_430 = lean_ctor_get(x_423, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_431 = x_423;
} else {
 lean_dec_ref(x_423);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_399);
lean_dec_ref(x_398);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_381);
lean_dec(x_361);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_22);
lean_dec_ref(x_7);
x_433 = lean_ctor_get(x_416, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_434 = x_416;
} else {
 lean_dec_ref(x_416);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_436 = lean_ctor_get(x_394, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_437 = x_394;
} else {
 lean_dec_ref(x_394);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec_ref(x_386);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_439 = lean_ctor_get(x_393, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_440 = x_393;
} else {
 lean_dec_ref(x_393);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_378);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_442 = lean_ctor_get(x_379, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_443 = x_379;
} else {
 lean_dec_ref(x_379);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_445 = lean_ctor_get(x_377, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_446 = x_377;
} else {
 lean_dec_ref(x_377);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec_ref(x_367);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_129);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_448 = lean_ctor_get(x_375, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_449 = x_375;
} else {
 lean_dec_ref(x_375);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_448);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_free_object(x_129);
lean_dec(x_107);
x_451 = lean_ctor_get(x_131, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_131, 1);
lean_inc(x_452);
lean_dec(x_131);
x_23 = x_451;
x_24 = x_114;
x_25 = x_109;
x_26 = x_110;
x_27 = x_113;
x_28 = x_111;
x_29 = x_452;
x_30 = x_116;
x_31 = x_120;
x_32 = x_117;
x_33 = x_119;
x_34 = x_115;
x_35 = x_112;
x_36 = lean_box(0);
goto block_104;
}
}
}
else
{
lean_object* x_453; 
x_453 = lean_ctor_get(x_129, 1);
lean_inc(x_453);
lean_dec(x_129);
if (x_2 == 0)
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_107);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_23 = x_454;
x_24 = x_114;
x_25 = x_109;
x_26 = x_110;
x_27 = x_113;
x_28 = x_111;
x_29 = x_455;
x_30 = x_116;
x_31 = x_120;
x_32 = x_117;
x_33 = x_119;
x_34 = x_115;
x_35 = x_112;
x_36 = lean_box(0);
goto block_104;
}
else
{
if (x_105 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_456 = x_1;
} else {
 lean_dec_ref(x_1);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_453, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_453, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_459 = x_453;
} else {
 lean_dec_ref(x_453);
 x_459 = lean_box(0);
}
lean_inc_ref(x_113);
x_460 = lean_array_to_list(x_113);
lean_inc(x_460);
lean_inc(x_16);
x_461 = l_Lean_mkConst(x_16, x_460);
x_462 = l_Lean_mkAppN(x_461, x_111);
lean_inc_ref(x_109);
x_463 = l_Lean_Expr_app___override(x_462, x_109);
x_464 = l_Lean_mkAppN(x_463, x_110);
x_465 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3;
lean_inc_ref(x_464);
x_466 = l_Lean_indentExpr(x_464);
x_467 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
x_468 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5;
x_469 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_470, 0, x_469);
lean_inc_ref(x_464);
x_471 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_471, 0, x_464);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_472 = l_Lean_Meta_mapErrorImp___redArg(x_471, x_470, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_472);
x_473 = lean_array_get_size(x_21);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_474 = l_Lean_Meta_inferArgumentTypesN(x_473, x_464, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec_ref(x_474);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_476 = lean_get_match_equations_for(x_16, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 2);
lean_inc_ref(x_479);
lean_dec(x_477);
lean_inc(x_478);
x_480 = l_Lean_mkConst(x_478, x_460);
x_481 = l_Lean_mkAppN(x_480, x_111);
lean_inc_ref(x_109);
x_482 = l_Lean_Expr_app___override(x_481, x_109);
x_483 = l_Lean_mkAppN(x_482, x_110);
x_484 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1;
lean_inc_ref(x_483);
x_485 = l_Lean_indentExpr(x_483);
x_486 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_468);
x_488 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 2, 1);
lean_closure_set(x_488, 0, x_487);
lean_inc_ref(x_483);
x_489 = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(x_489, 0, x_483);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_490 = l_Lean_Meta_mapErrorImp___redArg(x_489, x_488, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
lean_dec_ref(x_490);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_491 = l_Lean_Meta_inferArgumentTypesN(x_473, x_483, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
lean_dec_ref(x_491);
x_493 = lean_ctor_get(x_15, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_15, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_495);
x_496 = lean_ctor_get(x_15, 3);
lean_inc(x_496);
x_497 = lean_ctor_get(x_15, 5);
lean_inc_ref(x_497);
lean_dec_ref(x_15);
x_498 = lean_ctor_get(x_479, 2);
lean_inc_ref(x_498);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 lean_ctor_release(x_479, 3);
 lean_ctor_release(x_479, 4);
 lean_ctor_release(x_479, 5);
 x_499 = x_479;
} else {
 lean_dec_ref(x_479);
 x_499 = lean_box(0);
}
x_500 = lean_array_get_size(x_495);
x_501 = lean_array_get_size(x_498);
x_502 = lean_array_get_size(x_475);
x_503 = lean_array_get_size(x_492);
x_504 = l_Array_toSubarray___redArg(x_21, x_119, x_473);
lean_inc_ref(x_495);
x_505 = l_Array_toSubarray___redArg(x_495, x_119, x_500);
x_506 = l_Array_toSubarray___redArg(x_498, x_119, x_501);
x_507 = l_Array_toSubarray___redArg(x_475, x_119, x_502);
x_508 = l_Array_toSubarray___redArg(x_492, x_119, x_503);
if (lean_is_scalar(x_459)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_459;
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_120);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_506);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_505);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_504);
lean_ctor_set(x_513, 1, x_512);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
x_514 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_473, x_6, x_2, x_457, x_107, x_119, x_513, x_114, x_115, x_116, x_117);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
lean_dec_ref(x_514);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
lean_dec(x_516);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
lean_dec(x_517);
x_519 = lean_ctor_get(x_518, 1);
lean_inc(x_519);
lean_dec(x_518);
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_apply_6(x_7, x_22, x_114, x_115, x_116, x_117, lean_box(0));
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_523 = x_521;
} else {
 lean_dec_ref(x_521);
 x_523 = lean_box(0);
}
x_524 = l_Array_append___redArg(x_458, x_522);
lean_dec(x_522);
if (lean_is_scalar(x_499)) {
 x_525 = lean_alloc_ctor(0, 6, 0);
} else {
 x_525 = x_499;
}
lean_ctor_set(x_525, 0, x_493);
lean_ctor_set(x_525, 1, x_494);
lean_ctor_set(x_525, 2, x_495);
lean_ctor_set(x_525, 3, x_496);
lean_ctor_set(x_525, 4, x_112);
lean_ctor_set(x_525, 5, x_497);
if (lean_is_scalar(x_456)) {
 x_526 = lean_alloc_ctor(0, 8, 0);
} else {
 x_526 = x_456;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_478);
lean_ctor_set(x_526, 2, x_113);
lean_ctor_set(x_526, 3, x_111);
lean_ctor_set(x_526, 4, x_109);
lean_ctor_set(x_526, 5, x_110);
lean_ctor_set(x_526, 6, x_520);
lean_ctor_set(x_526, 7, x_524);
if (lean_is_scalar(x_523)) {
 x_527 = lean_alloc_ctor(0, 1, 0);
} else {
 x_527 = x_523;
}
lean_ctor_set(x_527, 0, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_520);
lean_dec(x_499);
lean_dec_ref(x_497);
lean_dec(x_496);
lean_dec_ref(x_495);
lean_dec(x_494);
lean_dec(x_493);
lean_dec(x_478);
lean_dec(x_458);
lean_dec(x_456);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
x_528 = lean_ctor_get(x_521, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_529 = x_521;
} else {
 lean_dec_ref(x_521);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_499);
lean_dec_ref(x_497);
lean_dec(x_496);
lean_dec_ref(x_495);
lean_dec(x_494);
lean_dec(x_493);
lean_dec(x_478);
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_22);
lean_dec_ref(x_7);
x_531 = lean_ctor_get(x_514, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 x_532 = x_514;
} else {
 lean_dec_ref(x_514);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 1, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_531);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_475);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_534 = lean_ctor_get(x_491, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 x_535 = x_491;
} else {
 lean_dec_ref(x_491);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_534);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec_ref(x_483);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_475);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_537 = lean_ctor_get(x_490, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_538 = x_490;
} else {
 lean_dec_ref(x_490);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 1, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_475);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_540 = lean_ctor_get(x_476, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_541 = x_476;
} else {
 lean_dec_ref(x_476);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_543 = lean_ctor_get(x_474, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 x_544 = x_474;
} else {
 lean_dec_ref(x_474);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec_ref(x_464);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_546 = lean_ctor_get(x_472, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_547 = x_472;
} else {
 lean_dec_ref(x_472);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 1, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_546);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_107);
x_549 = lean_ctor_get(x_453, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_453, 1);
lean_inc(x_550);
lean_dec(x_453);
x_23 = x_549;
x_24 = x_114;
x_25 = x_109;
x_26 = x_110;
x_27 = x_113;
x_28 = x_111;
x_29 = x_550;
x_30 = x_116;
x_31 = x_120;
x_32 = x_117;
x_33 = x_119;
x_34 = x_115;
x_35 = x_112;
x_36 = lean_box(0);
goto block_104;
}
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_551 = !lean_is_exclusive(x_128);
if (x_551 == 0)
{
return x_128;
}
else
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_128, 0);
lean_inc(x_552);
lean_dec(x_128);
x_553 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_553, 0, x_552);
return x_553;
}
}
}
block_595:
{
size_t x_561; size_t x_562; lean_object* x_563; 
x_561 = lean_array_size(x_18);
x_562 = 0;
lean_inc(x_559);
lean_inc_ref(x_558);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc_ref(x_18);
lean_inc_ref(x_4);
x_563 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(x_4, x_561, x_562, x_18, x_556, x_557, x_558, x_559);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; size_t x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = lean_array_size(x_20);
lean_inc(x_559);
lean_inc_ref(x_558);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc_ref(x_20);
x_566 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(x_4, x_565, x_562, x_20, x_556, x_557, x_558, x_559);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
lean_dec_ref(x_566);
x_568 = lean_box(x_3);
x_569 = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1;
lean_inc_ref(x_20);
lean_inc(x_567);
lean_inc_ref(x_15);
x_570 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(x_570, 0, x_5);
lean_closure_set(x_570, 1, x_15);
lean_closure_set(x_570, 2, x_567);
lean_closure_set(x_570, 3, x_568);
lean_closure_set(x_570, 4, x_569);
lean_closure_set(x_570, 5, x_20);
x_571 = 0;
lean_inc(x_559);
lean_inc_ref(x_558);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc_ref(x_19);
x_572 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(x_19, x_570, x_571, x_556, x_557, x_558, x_559);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
lean_dec_ref(x_572);
x_574 = lean_ctor_get(x_573, 1);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_15, 3);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_573, 0);
lean_inc(x_577);
lean_dec(x_573);
x_578 = lean_ctor_get(x_575, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_575, 1);
lean_inc(x_579);
lean_dec(x_575);
lean_inc_ref(x_17);
x_106 = x_562;
x_107 = x_555;
x_108 = x_578;
x_109 = x_577;
x_110 = x_567;
x_111 = x_564;
x_112 = x_579;
x_113 = x_17;
x_114 = x_556;
x_115 = x_557;
x_116 = x_558;
x_117 = x_559;
x_118 = lean_box(0);
goto block_554;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_inc(x_574);
x_580 = lean_ctor_get(x_573, 0);
lean_inc(x_580);
lean_dec(x_573);
x_581 = lean_ctor_get(x_574, 0);
lean_inc(x_581);
lean_dec(x_574);
x_582 = lean_ctor_get(x_575, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_575, 1);
lean_inc(x_583);
lean_dec(x_575);
x_584 = lean_ctor_get(x_576, 0);
lean_inc_ref(x_17);
x_585 = lean_array_set(x_17, x_584, x_581);
x_106 = x_562;
x_107 = x_555;
x_108 = x_582;
x_109 = x_580;
x_110 = x_567;
x_111 = x_564;
x_112 = x_583;
x_113 = x_585;
x_114 = x_556;
x_115 = x_557;
x_116 = x_558;
x_117 = x_559;
x_118 = lean_box(0);
goto block_554;
}
}
else
{
uint8_t x_586; 
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_559);
lean_dec_ref(x_558);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_586 = !lean_is_exclusive(x_572);
if (x_586 == 0)
{
return x_572;
}
else
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_572, 0);
lean_inc(x_587);
lean_dec(x_572);
x_588 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_588, 0, x_587);
return x_588;
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_564);
lean_dec(x_559);
lean_dec_ref(x_558);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_589 = !lean_is_exclusive(x_566);
if (x_589 == 0)
{
return x_566;
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_566, 0);
lean_inc(x_590);
lean_dec(x_566);
x_591 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_591, 0, x_590);
return x_591;
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_559);
lean_dec_ref(x_558);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_592 = !lean_is_exclusive(x_563);
if (x_592 == 0)
{
return x_563;
}
else
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_563, 0);
lean_inc(x_593);
lean_dec(x_563);
x_594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_594, 0, x_593);
return x_594;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed), 10, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 6);
x_12 = lean_ctor_get(x_1, 7);
x_13 = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
x_14 = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
x_15 = lean_array_get_size(x_12);
x_16 = 1;
x_17 = l_Lean_Meta_MatcherApp_inferMatchType___closed__2;
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_box(x_16);
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_11);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_11);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_10);
lean_closure_set(x_21, 7, x_9);
x_22 = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(x_1, x_16, x_18, x_13, x_21, x_17, x_14, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_17;
}
}
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6);
l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1 = _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1();
lean_mark_persistent(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1);
l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__5);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__6);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__7);
l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__4);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__5);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__6);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__7);
l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___closed__9);
l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__5);
l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3);
l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1 = _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0 = _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0 = _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1 = _init_l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1);
l_Lean_Meta_MatcherApp_inferMatchType___closed__2 = _init_l_Lean_Meta_MatcherApp_inferMatchType___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
