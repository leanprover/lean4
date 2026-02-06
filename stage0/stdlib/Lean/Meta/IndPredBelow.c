// Lean compiler output
// Module: Lean.Meta.IndPredBelow
// Imports: public import Lean.Meta.Match.MatcherApp.Basic import Lean.Meta.Constructions.CasesOn import Lean.Meta.Match.Match import Init.Data.Nat.Linear import Init.Omega
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
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__1(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.IndPredBelow"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__0_value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.IndPredBelow.0.Lean.Meta.IndPredBelow.ihTypeToBelowType"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ih"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 60, 57, 160, 49, 55, 75, 124)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1;
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__List_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__List_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 86, 156, 132, 67, 140, 213, 247)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__1_value;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "brecOn"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 218, 162, 241, 241, 188, 88, 49)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "below"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 30, 178, 229, 0, 2, 121, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 106, 38, 217, 182, 144, 186, 220)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__2_value;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__5_value;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__0_value;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1;
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__1_value;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_IndPredBelow_mkBelow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__0 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__0_value;
static const lean_string_object l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__1 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value;
static const lean_string_object l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "IndPredBelow"};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__2 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_IndPredBelow_mkBelow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_IndPredBelow_mkBelow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 254, 232, 239, 205, 163, 68, 56)}};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__3 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__3_value;
static const lean_string_object l_Lean_Meta_IndPredBelow_mkBelow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__4 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__4_value;
static double l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__1(lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__1_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__4(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__5(lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nBelows:\n"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__1_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__4 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__4_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__5 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__5_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__6 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__6_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__7 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__7_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__8 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__8_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__9 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__9_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__10 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__4_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__11 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__11_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__6_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__7_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__8_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__9_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__12 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__12_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13_value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nMotives:\n"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__14 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__14_value)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__15 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__15_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16;
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__1 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__3, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__3 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__4 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__5, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__5 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__0_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__1_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__2_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__3_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__4_value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__5_value)} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__6 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__6_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_below_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_below_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_motive_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_motive_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Below: "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__2_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Motive: "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__5_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_fvar___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_getDecl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_getDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern_go(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expected constant application at "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__0_value;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__0_value;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__2_value;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " pattern "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__2_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3;
lean_object* l_Lean_exceptEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__1_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 254, 232, 239, 205, 163, 68, 56)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 235, 50, 143, 1, 114, 90, 167)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rec indices "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__2_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instantiate "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__7 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__7_value;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "transform "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__3_value;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern_default;
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid amount of patterns"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__0_value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0;
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__0_value;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1;
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "alt "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__0_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__2_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__4_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "oldCount = "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__6_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "; fvars = "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__8_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__10_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__11 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__11_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "new decls:\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__16 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__16_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17;
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___boxed(lean_object**);
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0;
extern lean_object* l_Lean_Meta_Match_instInhabitedAltLHS_default;
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0;
static const lean_ctor_object l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1_value;
lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__0_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__0_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__0_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__1_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__0_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__1_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__1_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__3_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__1_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__3_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__3_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__4_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__3_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__4_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__4_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__5_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__4_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 106, 83, 242, 18, 155, 172, 143)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__5_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__5_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__6_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__5_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(94, 80, 212, 250, 147, 0, 251, 8)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__6_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__6_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__7_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__6_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 126, 199, 123, 88, 217, 245, 201)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__7_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__7_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__8_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__7_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 54, 192, 161, 104, 141, 102, 124)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__8_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__8_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__9_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__8_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 48, 169, 169, 84, 43, 72, 34)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__9_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__9_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__10_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__10_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__10_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__11_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__9_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__10_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 218, 79, 11, 233, 34, 24, 64)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__11_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__11_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__12_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__12_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__12_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__13_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__11_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__12_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 4, 126, 179, 243, 245, 197, 86)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__13_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__13_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__14_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__13_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__2_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 169, 238, 209, 152, 212, 174, 82)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__14_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__14_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__15_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__14_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 251, 153, 44, 240, 170, 172, 87)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__15_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__15_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__16_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__15_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_IndPredBelow_mkBelow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 50, 158, 122, 189, 32, 146, 77)}};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__16_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__16_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__18_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__18_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__18_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__20_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__20_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__20_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_getForallBody(x_1);
x_4 = l_Lean_Expr_getAppFn(x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_param___override(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_param___override(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = lean_box(0);
x_8 = lean_array_get(x_7, x_6, x_1);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx_spec__0(x_3, x_9);
x_11 = l_Lean_Expr_const___override(x_8, x_10);
x_12 = l_Lean_mkAppN(x_11, x_4);
lean_dec_ref(x_4);
x_13 = l_Lean_mkAppN(x_12, x_5);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(227u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = l_Lean_Name_quickCmp(x_3, x_4);
switch (x_8) {
case 0:
{
x_2 = x_6;
goto _start;
}
case 1:
{
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
default: 
{
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3;
x_12 = lean_panic_fn(x_1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(75u);
x_4 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(x_5, x_4, x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(x_6, x_2);
lean_dec(x_6);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(x_8, x_2);
x_11 = l_Lean_Expr_app___override(x_10, x_9);
return x_11;
}
case 7:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_16 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(x_14, x_2);
x_17 = l_Lean_Expr_forallE___override(x_12, x_13, x_16, x_15);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3;
x_19 = l_panic___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__1(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; size_t x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_6 = 1;
lean_inc_ref(x_2);
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit(x_2);
x_13 = lean_ptr_addr(x_4);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
x_8 = x_14;
goto block_12;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_2);
x_16 = lean_ptr_addr(x_7);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_8 = x_17;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc_ref(x_4);
lean_inc(x_3);
lean_dec_ref(x_1);
x_9 = l_Lean_Expr_forallE___override(x_3, x_4, x_7, x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_instBEqBinderInfo_beq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc_ref(x_4);
lean_inc(x_3);
lean_dec_ref(x_1);
x_11 = l_Lean_Expr_forallE___override(x_3, x_4, x_7, x_6);
return x_11;
}
else
{
lean_dec_ref(x_7);
return x_1;
}
}
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec_ref(x_4);
x_12 = lean_box(x_11);
x_13 = lean_box(x_7);
x_14 = lean_apply_7(x_2, x_5, x_6, x_8, x_9, x_10, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_2(x_3, x_1, lean_box(0));
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_apply_2(x_3, x_1, lean_box(0));
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec_ref(x_5);
x_13 = lean_box(x_12);
x_14 = lean_box(x_8);
x_15 = lean_apply_7(x_3, x_6, x_7, x_9, x_10, x_11, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_apply_2(x_4, x_2, lean_box(0));
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_apply_2(x_4, x_2, lean_box(0));
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(x_3, x_1);
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_5, x_13, x_12, x_14, x_14, x_15, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_17);
x_18 = lean_infer_type(x_17, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH(x_19, x_1);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_20);
lean_inc(x_17);
x_21 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__1));
lean_inc(x_9);
lean_inc_ref(x_8);
x_22 = l_Lean_Core_mkFreshUserName(x_21, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_1);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0___boxed), 12, 6);
lean_closure_set(x_24, 0, x_4);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_17);
lean_closure_set(x_24, 3, x_1);
lean_closure_set(x_24, 4, x_2);
lean_closure_set(x_24, 5, x_3);
x_25 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(x_19, x_1);
x_26 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_23, x_25, x_24, x_6, x_7, x_8, x_9);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_19);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
lean_inc(x_17);
x_32 = lean_array_push(x_5, x_17);
x_4 = x_31;
x_5 = x_32;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = lean_array_push(x_2, x_7);
x_16 = lean_array_push(x_15, x_3);
x_17 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go(x_4, x_5, x_6, x_14, x_16, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go(x_1, x_3, x_4, x_10, x_2, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_array_get_borrowed(x_18, x_14, x_13);
x_20 = l_Lean_Expr_fvarId_x21(x_19);
lean_inc_ref(x_6);
x_21 = l_Lean_FVarId_getUserName___redArg(x_20, x_6, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_19);
x_23 = lean_infer_type(x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Expr_getForallBody(x_25);
x_27 = l_Lean_Expr_getAppFn(x_26);
lean_dec_ref(x_26);
x_28 = lean_expr_eqv(x_27, x_2);
lean_dec_ref(x_27);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_free_object(x_23);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_29 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0___boxed), 9, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_3);
x_30 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_31 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_25, x_29, x_30, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_inc(x_4);
x_33 = l_Lean_Name_append(x_4, x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_12, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_13, x_36);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_37);
lean_ctor_set(x_5, 0, x_35);
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = l_Lean_Expr_getForallBody(x_42);
x_44 = l_Lean_Expr_getAppFn(x_43);
lean_dec_ref(x_43);
x_45 = lean_expr_eqv(x_44, x_2);
lean_dec_ref(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_5);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_47 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0___boxed), 9, 2);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_3);
x_48 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_49 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_42, x_47, x_48, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_4);
x_51 = l_Lean_Name_append(x_4, x_22);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_array_push(x_12, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_13, x_54);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_55);
lean_ctor_set(x_5, 0, x_53);
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_58 = x_49;
} else {
 lean_dec_ref(x_49);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_23, 0);
lean_inc(x_61);
lean_dec(x_23);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
return x_21;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_21, 0);
lean_inc(x_64);
lean_dec(x_21);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_5, 0);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_5);
x_68 = lean_ctor_get(x_1, 4);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_67, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l_Lean_instInhabitedExpr;
x_74 = lean_array_get_borrowed(x_73, x_68, x_67);
x_75 = l_Lean_Expr_fvarId_x21(x_74);
lean_inc_ref(x_6);
x_76 = l_Lean_FVarId_getUserName___redArg(x_75, x_6, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_74);
x_78 = lean_infer_type(x_74, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Expr_getForallBody(x_79);
x_82 = l_Lean_Expr_getAppFn(x_81);
lean_dec_ref(x_81);
x_83 = lean_expr_eqv(x_82, x_2);
lean_dec_ref(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_66);
lean_ctor_set(x_84, 1, x_67);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
lean_dec(x_80);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_86 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___lam__0___boxed), 9, 2);
lean_closure_set(x_86, 0, x_1);
lean_closure_set(x_86, 1, x_3);
x_87 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_88 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_79, x_86, x_87, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
lean_inc(x_4);
x_90 = l_Lean_Name_append(x_4, x_77);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_push(x_66, x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_67, x_93);
lean_dec(x_67);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_5 = x_95;
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_98 = x_88;
} else {
 lean_dec_ref(x_88);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_77);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_101 = x_78;
} else {
 lean_dec_ref(x_78);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_76, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_104 = x_76;
} else {
 lean_dec_ref(x_76);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 6);
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get(x_12, x_10, x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_13);
x_14 = lean_infer_type(x_13, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_9);
x_16 = l_Array_append___redArg(x_9, x_10);
x_17 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_toImplicit(x_15);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkForallFVars(x_16, x_17, x_18, x_19, x_19, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_box(0);
x_24 = lean_array_get(x_23, x_11, x_1);
x_25 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_2);
lean_inc(x_24);
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__1(x_3, x_13, x_16, x_24, x_26, x_4, x_5, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_array_to_list(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_29, 0, x_32);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_array_to_list(x_35);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_27, 0, x_39);
return x_27;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_array_to_list(x_41);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_22);
lean_ctor_set(x_45, 2, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_22);
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_21, 0);
lean_inc(x_52);
lean_dec(x_21);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = l_Lean_mkCasesOn(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec_ref(x_13);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_3, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_15 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive(x_3, x_14, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_13, x_18);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_28 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive(x_3, x_27, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_3, x_34);
lean_dec(x_3);
x_3 = x_35;
x_4 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_38 = x_28;
} else {
 lean_dec_ref(x_28);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_10);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg(x_11, x_1, x_12, x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
x_18 = lean_nat_add(x_17, x_11);
x_19 = lean_array_to_list(x_16);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
lean_inc(x_5);
lean_inc_ref(x_4);
x_22 = l_Lean_addDecl(x_21, x_20, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
lean_dec_ref(x_22);
x_23 = lean_box(0);
x_24 = lean_array_size(x_10);
x_25 = 0;
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__0(x_10, x_24, x_25, x_23, x_2, x_3, x_4, x_5);
lean_dec_ref(x_10);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_23);
return x_29;
}
}
else
{
return x_26;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_22;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get_borrowed(x_12, x_1, x_2);
x_14 = l_Lean_Expr_updateFn(x_6, x_13);
x_15 = l_Lean_mkAppN(x_3, x_5);
x_16 = l_Lean_Expr_app___override(x_14, x_15);
x_17 = 0;
x_18 = 1;
x_19 = l_Lean_Meta_mkLambdaFVars(x_5, x_16, x_17, x_4, x_17, x_4, x_18, x_7, x_8, x_9, x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_box(0);
x_19 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx_spec__0(x_15, x_18);
x_20 = l_Lean_Expr_const___override(x_3, x_19);
x_21 = l_Lean_mkAppN(x_20, x_16);
lean_dec_ref(x_16);
x_22 = l_Lean_mkAppN(x_21, x_17);
lean_dec_ref(x_17);
x_23 = l_Lean_mkAppN(x_22, x_7);
lean_dec_ref(x_7);
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_6, x_23, x_14, x_24, x_14, x_24, x_25, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_array_fget_borrowed(x_4, x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_27);
x_28 = lean_infer_type(x_27, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH(x_29, x_1);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
x_33 = l_Lean_Core_mkFreshUserName(x_32, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_box(x_14);
lean_inc_ref(x_1);
lean_inc(x_29);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1___boxed), 16, 10);
lean_closure_set(x_36, 0, x_2);
lean_closure_set(x_36, 1, x_31);
lean_closure_set(x_36, 2, x_35);
lean_closure_set(x_36, 3, x_29);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_7);
lean_closure_set(x_36, 7, x_1);
lean_closure_set(x_36, 8, x_3);
lean_closure_set(x_36, 9, x_4);
x_37 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType(x_29, x_1);
x_38 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_34, x_37, x_36, x_8, x_9, x_10, x_11);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
lean_dec(x_29);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_5, x_42);
lean_dec(x_5);
lean_inc(x_27);
x_44 = lean_array_push(x_6, x_27);
lean_inc(x_27);
x_45 = lean_array_push(x_7, x_27);
x_5 = x_43;
x_6 = x_44;
x_7 = x_45;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_box(x_3);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___lam__0___boxed), 11, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_17);
x_19 = 0;
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_20 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_4, x_18, x_19, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_inc_ref(x_11);
x_24 = lean_array_push(x_6, x_11);
x_25 = lean_array_push(x_7, x_11);
x_26 = lean_array_push(x_25, x_21);
x_27 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2(x_8, x_1, x_9, x_10, x_23, x_24, x_26, x_12, x_13, x_14, x_15);
return x_27;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__List_map__unattach_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__List_map__unattach_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_5, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(x_1, x_2);
x_13 = l_Lean_mkAppN(x_12, x_5);
x_14 = l_Lean_mkAppN(x_3, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
x_15 = l_Lean_mkArrow(x_13, x_14, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = 0;
x_18 = 1;
x_19 = l_Lean_Meta_mkForallFVars(x_5, x_16, x_17, x_4, x_4, x_18, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_19;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_5);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_go2(x_1, x_2, x_3, x_6, x_4, x_5, x_5, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
return x_13;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_14);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Expr_fvarId_x21(x_14);
lean_dec(x_14);
lean_inc_ref(x_7);
x_18 = l_Lean_FVarId_getUserName___redArg(x_17, x_7, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_1, 6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0;
x_24 = l_Lean_Expr_getForallBody(x_16);
x_25 = l_Lean_Expr_getAppFn(x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec_ref(x_25);
x_27 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg(x_22, x_20, x_26);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_array_get_borrowed(x_28, x_21, x_27);
lean_dec(x_27);
lean_inc(x_29);
x_30 = l_Lean_Name_append(x_29, x_19);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___lam__0___boxed), 12, 5);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_30);
lean_closure_set(x_31, 3, x_22);
lean_closure_set(x_31, 4, x_23);
x_32 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_33 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_16, x_31, x_32, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_array_push(x_6, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
x_6 = x_35;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc_ref(x_1);
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx(x_6, x_1);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_inc_ref(x_10);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0;
x_16 = lean_array_size(x_12);
x_17 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0(x_2, x_4, x_12, x_16, x_17, x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Array_range(x_13);
x_21 = lean_array_size(x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__1(x_2, x_21, x_17, x_20);
x_23 = l_Array_append___redArg(x_10, x_22);
lean_dec_ref(x_22);
x_24 = l_Array_append___redArg(x_23, x_19);
lean_dec(x_19);
x_25 = lean_apply_7(x_1, x_4, x_24, x_5, x_6, x_7, x_8, lean_box(0));
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_fget_borrowed(x_11, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_29);
x_30 = lean_infer_type(x_29, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_box(x_14);
lean_inc(x_29);
lean_inc_ref(x_2);
lean_inc(x_3);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__0___boxed), 11, 4);
lean_closure_set(x_33, 0, x_3);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_29);
lean_closure_set(x_33, 3, x_32);
x_34 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_35 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_31, x_33, x_34, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___closed__1));
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
lean_dec(x_3);
lean_inc(x_39);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1___boxed), 10, 4);
lean_closure_set(x_40, 0, x_4);
lean_closure_set(x_40, 1, x_1);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_39);
x_41 = lean_name_append_index_after(x_37, x_39);
x_42 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_41, x_36, x_40, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_30, 0);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_5);
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0;
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go(x_1, x_2, x_8, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = l_Lean_LocalContext_setBinderInfo(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_4, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_mkForallFVars(x_1, x_6, x_3, x_4, x_4, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_array_get_borrowed(x_7, x_8, x_9);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_addDecl(x_25, x_3, x_13, x_14);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0(x_1, x_2, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_14, 2);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_12);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_44, x_45);
x_47 = lean_nat_dec_lt(x_43, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_inc_ref(x_42);
x_19 = x_42;
goto block_41;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_44);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_46);
x_49 = lean_nat_dec_lt(x_43, x_44);
if (x_49 == 0)
{
lean_inc_ref(x_42);
x_19 = x_42;
goto block_41;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
lean_inc_ref(x_42);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1(x_12, x_50, x_51, x_42);
x_19 = x_52;
goto block_41;
}
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_46);
lean_dec(x_46);
lean_inc_ref(x_42);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__1(x_12, x_53, x_54, x_42);
x_19 = x_55;
goto block_41;
}
}
block_41:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
lean_inc(x_2);
x_23 = lean_array_get(x_2, x_21, x_3);
lean_dec_ref(x_21);
x_24 = l_Lean_Expr_const___override(x_23, x_4);
x_25 = l_Lean_mkAppN(x_24, x_5);
x_26 = l_Lean_mkAppN(x_25, x_12);
x_27 = lean_array_get_borrowed(x_6, x_7, x_3);
lean_inc(x_27);
x_28 = l_Lean_mkAppN(x_27, x_12);
x_29 = l_Lean_Expr_app___override(x_28, x_26);
x_30 = l_Lean_mkAppN(x_8, x_12);
x_31 = l_Array_append___redArg(x_20, x_9);
x_32 = l_Array_append___redArg(x_31, x_12);
x_33 = l_Array_append___redArg(x_32, x_7);
x_34 = 0;
x_35 = 1;
x_36 = lean_box(x_34);
x_37 = lean_box(x_10);
x_38 = lean_box(x_35);
x_39 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__0___boxed), 15, 10);
lean_closure_set(x_39, 0, x_33);
lean_closure_set(x_39, 1, x_29);
lean_closure_set(x_39, 2, x_36);
lean_closure_set(x_39, 3, x_37);
lean_closure_set(x_39, 4, x_38);
lean_closure_set(x_39, 5, x_30);
lean_closure_set(x_39, 6, x_2);
lean_closure_set(x_39, 7, x_22);
lean_closure_set(x_39, 8, x_3);
lean_closure_set(x_39, 9, x_11);
x_40 = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__0___redArg(x_19, x_39, x_14, x_15, x_16, x_17);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_10);
x_20 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_8, x_1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get_borrowed(x_17, x_2, x_8);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_18);
x_19 = lean_infer_type(x_18, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_box(0);
x_22 = lean_box(x_15);
lean_inc(x_7);
lean_inc_ref(x_2);
lean_inc(x_18);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_8);
lean_inc_ref(x_3);
x_23 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___lam__1___boxed), 18, 11);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_8);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_17);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_18);
lean_closure_set(x_23, 8, x_2);
lean_closure_set(x_23, 9, x_22);
lean_closure_set(x_23, 10, x_7);
x_24 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_25 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_20, x_23, x_24, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_25);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_8, x_27);
lean_dec(x_8);
x_8 = x_28;
x_9 = x_26;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_25;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_array_get_size(x_11);
x_21 = lean_box(0);
lean_inc(x_9);
x_22 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowAppOfIdx_spec__0(x_9, x_21);
if (x_10 == 0)
{
x_13 = x_22;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_13 = x_24;
goto block_20;
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg(x_12, x_11, x_1, x_13, x_3, x_2, x_9, x_14, x_15, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___lam__0___boxed), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2___boxed(lean_object** _args) {
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
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__1));
x_9 = l_Lean_Name_append(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_name_append_index_after(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1));
x_9 = l_Lean_Name_append(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1));
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Name_append(x_6, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_10 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_9, x_8, x_4);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_17 = l_Array_extract___redArg(x_9, x_16, x_1);
lean_inc(x_2);
x_18 = l_Array_extract___redArg(x_9, x_1, x_2);
x_19 = lean_array_get_size(x_9);
x_20 = l_Array_extract___redArg(x_9, x_2, x_19);
x_47 = lean_box(1);
x_48 = l_Array_zipIdx___redArg(x_18, x_16);
x_49 = lean_array_get_size(x_48);
x_50 = lean_nat_dec_lt(x_16, x_49);
if (x_50 == 0)
{
lean_dec_ref(x_48);
x_21 = x_47;
goto block_46;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_dec_ref(x_48);
x_21 = x_47;
goto block_46;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_49);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6(x_48, x_52, x_53, x_47);
lean_dec_ref(x_48);
x_21 = x_54;
goto block_46;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_49);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_IndPredBelow_mkBelow_spec__6(x_48, x_55, x_56, x_47);
lean_dec_ref(x_48);
x_21 = x_57;
goto block_46;
}
}
block_46:
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_3);
x_22 = lean_array_mk(x_3);
x_23 = lean_array_size(x_22);
x_24 = 0;
lean_inc_ref(x_22);
x_25 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2(x_23, x_24, x_22);
x_26 = l_List_head_x21___redArg(x_4, x_3);
lean_dec(x_3);
lean_inc(x_26);
x_27 = l_Lean_Name_append(x_26, x_5);
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Array_range_x27(x_28, x_6, x_28);
x_30 = lean_array_size(x_29);
lean_inc_ref(x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(x_27, x_30, x_24, x_29);
x_32 = l_Array_append___redArg(x_25, x_31);
lean_dec_ref(x_31);
lean_inc_ref(x_22);
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4(x_23, x_24, x_22);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1));
lean_inc(x_26);
x_35 = l_Lean_Name_append(x_26, x_34);
lean_inc_ref(x_29);
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(x_35, x_30, x_24, x_29);
x_37 = l_Array_append___redArg(x_33, x_36);
lean_dec_ref(x_36);
x_38 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5(x_23, x_24, x_22);
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__5___closed__1));
x_40 = l_Lean_Name_append(x_26, x_39);
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__3(x_40, x_30, x_24, x_29);
x_42 = l_Array_append___redArg(x_38, x_41);
lean_dec_ref(x_41);
x_43 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_17);
lean_ctor_set(x_43, 2, x_18);
lean_ctor_set(x_43, 3, x_21);
lean_ctor_set(x_43, 4, x_20);
lean_ctor_set(x_43, 5, x_32);
lean_ctor_set(x_43, 6, x_37);
lean_ctor_set(x_43, 7, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*8, x_8);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
x_44 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives(x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
x_45 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBRecOn(x_43, x_11, x_12, x_13, x_14);
return x_45;
}
else
{
lean_dec_ref(x_43);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_8);
x_17 = l_Lean_Meta_IndPredBelow_mkBelow___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofName(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkBelow___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0;
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
x_18 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_19 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
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
x_36 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_37 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
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
x_44 = lean_box(0);
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
x_52 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_53 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
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
x_61 = lean_box(0);
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
x_71 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_72 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
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
x_81 = lean_box(0);
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
x_89 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_90 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
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
x_106 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_107 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
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
x_116 = lean_box(0);
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
x_126 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_127 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
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
x_144 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_145 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
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
x_154 = lean_box(0);
x_155 = l_instInhabitedOfMonad___redArg(x_153, x_154);
x_156 = lean_panic_fn(x_155, x_1);
x_157 = lean_apply_5(x_156, x_2, x_3, x_4, x_5, lean_box(0));
return x_157;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(128u);
x_4 = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__5));
x_5 = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_st_ref_get(x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_1);
x_19 = l_Lean_Environment_findAsync_x3f(x_17, x_1, x_18);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
if (x_21 == 7)
{
lean_object* x_22; 
x_22 = l_Lean_AsyncConstantInfo_toConstantInfo(x_20);
if (lean_obj_tag(x_22) == 7)
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 0);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_22);
x_26 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2(x_26, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_27);
x_7 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
if (lean_obj_tag(x_31) == 0)
{
x_7 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
lean_dec(x_20);
x_7 = lean_box(0);
goto block_15;
}
}
else
{
lean_dec(x_19);
x_7 = lean_box(0);
goto block_15;
}
block_15:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1;
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_1, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_13, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_Lean_isInductiveCore_x3f(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1;
x_11 = 0;
x_12 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_15, x_2, x_3, x_4, x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_ctor_set_tag(x_9, 0);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_st_ref_get(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_replaceRef(x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_20, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_st_ref_take(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Lean_PersistentArray_push___redArg(x_1, x_29);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_8, x_24);
x_32 = lean_box(0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_23);
x_35 = l_Lean_PersistentArray_push___redArg(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_33);
lean_ctor_set(x_24, 4, x_36);
x_37 = lean_st_ref_set(x_8, x_24);
x_38 = lean_box(0);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 5);
x_45 = lean_ctor_get(x_24, 6);
x_46 = lean_ctor_get(x_24, 7);
x_47 = lean_ctor_get(x_24, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_48 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_23);
x_51 = l_Lean_PersistentArray_push___redArg(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 8);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint64(x_52, sizeof(void*)*1, x_48);
x_53 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_44);
lean_ctor_set(x_53, 6, x_45);
lean_ctor_set(x_53, 7, x_46);
lean_ctor_set(x_53, 8, x_47);
x_54 = lean_st_ref_set(x_8, x_53);
x_55 = lean_box(0);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
lean_dec(x_21);
x_57 = lean_st_ref_take(x_8);
x_58 = lean_ctor_get(x_57, 4);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_57, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_57, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_57, 8);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get_uint64(x_58, sizeof(void*)*1);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_56);
x_71 = l_Lean_PersistentArray_push___redArg(x_1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 9, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_63);
lean_ctor_set(x_73, 6, x_64);
lean_ctor_set(x_73, 7, x_65);
lean_ctor_set(x_73, 8, x_66);
x_74 = lean_st_ref_set(x_8, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
x_79 = lean_ctor_get(x_7, 2);
x_80 = lean_ctor_get(x_7, 3);
x_81 = lean_ctor_get(x_7, 4);
x_82 = lean_ctor_get(x_7, 5);
x_83 = lean_ctor_get(x_7, 6);
x_84 = lean_ctor_get(x_7, 7);
x_85 = lean_ctor_get(x_7, 8);
x_86 = lean_ctor_get(x_7, 9);
x_87 = lean_ctor_get(x_7, 10);
x_88 = lean_ctor_get(x_7, 11);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_90 = lean_ctor_get(x_7, 12);
x_91 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_92 = lean_ctor_get(x_7, 13);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_93 = lean_st_ref_get(x_8);
x_94 = lean_ctor_get(x_93, 4);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_replaceRef(x_3, x_82);
lean_dec(x_82);
x_97 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
lean_ctor_set(x_97, 9, x_86);
lean_ctor_set(x_97, 10, x_87);
lean_ctor_set(x_97, 11, x_88);
lean_ctor_set(x_97, 12, x_90);
lean_ctor_set(x_97, 13, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*14, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*14 + 1, x_91);
x_98 = l_Lean_PersistentArray_toArray___redArg(x_95);
lean_dec_ref(x_95);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(x_99, x_100, x_98);
x_102 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_4);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_102, x_5, x_6, x_97, x_8);
lean_dec_ref(x_97);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_st_ref_take(x_8);
x_107 = lean_ctor_get(x_106, 4);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_106, 5);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_106, 6);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_106, 7);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_106, 8);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get_uint64(x_107, sizeof(void*)*1);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_104);
x_120 = l_Lean_PersistentArray_push___redArg(x_1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint64(x_121, sizeof(void*)*1, x_117);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_109);
lean_ctor_set(x_122, 2, x_110);
lean_ctor_set(x_122, 3, x_111);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_112);
lean_ctor_set(x_122, 6, x_113);
lean_ctor_set(x_122, 7, x_114);
lean_ctor_set(x_122, 8, x_115);
x_123 = lean_st_ref_set(x_8, x_122);
x_124 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_105;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_48; double x_81; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lean_trace_profiler;
x_33 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_4, x_32);
if (x_33 == 0)
{
x_48 = x_33;
goto block_80;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_trace_profiler_useHeartbeats;
x_88 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_4, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; double x_91; double x_92; double x_93; 
x_89 = l_Lean_trace_profiler_threshold;
x_90 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(x_4, x_89);
x_91 = lean_float_of_nat(x_90);
x_92 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3;
x_93 = lean_float_div(x_91, x_92);
x_81 = x_93;
goto block_86;
}
else
{
lean_object* x_94; lean_object* x_95; double x_96; 
x_94 = l_Lean_trace_profiler_threshold;
x_95 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(x_4, x_94);
x_96 = lean_float_of_nat(x_95);
x_81 = x_96;
goto block_86;
}
}
block_29:
{
lean_object* x_24; 
x_24 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13(x_6, x_18, x_17, x_16, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_14);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
block_42:
{
double x_37; lean_object* x_38; 
x_37 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
lean_inc_ref(x_3);
lean_inc(x_1);
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_2);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_35;
x_17 = x_34;
x_18 = x_38;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_39; double x_40; double x_41; 
lean_dec_ref(x_38);
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_unbox_float(x_30);
lean_dec(x_30);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_40);
x_41 = lean_unbox_float(x_31);
lean_dec(x_31);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_41);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_2);
x_16 = x_35;
x_17 = x_34;
x_18 = x_39;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_44 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_43);
x_34 = x_43;
x_35 = x_45;
x_36 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_44);
x_46 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2;
lean_inc(x_43);
x_34 = x_43;
x_35 = x_46;
x_36 = lean_box(0);
goto block_42;
}
}
block_80:
{
if (x_5 == 0)
{
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_49 = lean_st_ref_take(x_12);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = l_Lean_PersistentArray_append___redArg(x_6, x_53);
lean_dec_ref(x_53);
lean_ctor_set(x_51, 0, x_54);
x_55 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_56 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_14);
return x_56;
}
else
{
uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get_uint64(x_51, sizeof(void*)*1);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_PersistentArray_append___redArg(x_6, x_58);
lean_dec_ref(x_58);
x_60 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_57);
lean_ctor_set(x_49, 4, x_60);
x_61 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_62 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_14);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
x_66 = lean_ctor_get(x_49, 2);
x_67 = lean_ctor_get(x_49, 3);
x_68 = lean_ctor_get(x_49, 5);
x_69 = lean_ctor_get(x_49, 6);
x_70 = lean_ctor_get(x_49, 7);
x_71 = lean_ctor_get(x_49, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_63);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_72 = lean_ctor_get_uint64(x_63, sizeof(void*)*1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = l_Lean_PersistentArray_append___redArg(x_6, x_73);
lean_dec_ref(x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 8);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint64(x_76, sizeof(void*)*1, x_72);
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_68);
lean_ctor_set(x_77, 6, x_69);
lean_ctor_set(x_77, 7, x_70);
lean_ctor_set(x_77, 8, x_71);
x_78 = lean_st_ref_set(x_12, x_77);
lean_dec(x_12);
x_79 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_14);
return x_79;
}
}
else
{
goto block_47;
}
}
else
{
goto block_47;
}
}
block_86:
{
double x_82; double x_83; double x_84; uint8_t x_85; 
x_82 = lean_unbox_float(x_31);
x_83 = lean_unbox_float(x_30);
x_84 = lean_float_sub(x_82, x_83);
x_85 = lean_float_decLt(x_81, x_84);
x_48 = x_85;
goto block_80;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
static double _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_13 = lean_box(0);
if (x_12 == 0)
{
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = lean_box(0);
goto block_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_303; 
x_113 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__3));
x_114 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_113, x_4);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
lean_inc(x_1);
x_117 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelow___lam__1___boxed), 7, 1);
lean_closure_set(x_117, 0, x_1);
x_118 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_303 = lean_unbox(x_115);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = l_Lean_trace_profiler;
x_305 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_11, x_304);
if (x_305 == 0)
{
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = lean_box(0);
goto block_112;
}
else
{
lean_inc_ref(x_11);
goto block_302;
}
}
else
{
lean_inc_ref(x_11);
goto block_302;
}
block_135:
{
lean_object* x_123; double x_124; double x_125; double x_126; double x_127; double x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_123 = lean_io_mono_nanos_now();
x_124 = lean_float_of_nat(x_119);
x_125 = l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
x_126 = lean_float_div(x_124, x_125);
x_127 = lean_float_of_nat(x_123);
x_128 = lean_float_div(x_127, x_125);
x_129 = lean_box_float(x_126);
x_130 = lean_box_float(x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_unbox(x_115);
lean_dec(x_115);
x_134 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_113, x_12, x_118, x_11, x_133, x_120, x_117, x_132, x_2, x_3, x_4, x_5);
lean_dec_ref(x_11);
return x_134;
}
block_141:
{
lean_object* x_140; 
if (lean_is_scalar(x_116)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_116;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_138);
x_119 = x_136;
x_120 = x_137;
x_121 = x_140;
x_122 = lean_box(0);
goto block_135;
}
block_146:
{
lean_object* x_145; 
x_145 = lean_box(0);
x_136 = x_143;
x_137 = x_144;
x_138 = x_145;
x_139 = lean_box(0);
goto block_141;
}
block_152:
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_149);
x_119 = x_147;
x_120 = x_148;
x_121 = x_151;
x_122 = lean_box(0);
goto block_135;
}
block_175:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_nat_add(x_160, x_164);
lean_dec(x_164);
lean_dec(x_160);
x_168 = lean_box(x_153);
lean_inc(x_167);
x_169 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelow___lam__0___boxed), 15, 8);
lean_closure_set(x_169, 0, x_155);
lean_closure_set(x_169, 1, x_167);
lean_closure_set(x_169, 2, x_154);
lean_closure_set(x_169, 3, x_13);
lean_closure_set(x_169, 4, x_156);
lean_closure_set(x_169, 5, x_157);
lean_closure_set(x_169, 6, x_158);
lean_closure_set(x_169, 7, x_168);
x_170 = lean_nat_add(x_167, x_159);
lean_dec(x_159);
lean_dec(x_167);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_172 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(x_166, x_171, x_169, x_162, x_162, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_136 = x_163;
x_137 = x_165;
x_138 = x_173;
x_139 = lean_box(0);
goto block_141;
}
else
{
lean_object* x_174; 
lean_dec(x_116);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec_ref(x_172);
x_147 = x_163;
x_148 = x_165;
x_149 = x_174;
x_150 = lean_box(0);
goto block_152;
}
}
block_189:
{
lean_object* x_180; double x_181; double x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_180 = lean_io_get_num_heartbeats();
x_181 = lean_float_of_nat(x_176);
x_182 = lean_float_of_nat(x_180);
x_183 = lean_box_float(x_181);
x_184 = lean_box_float(x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_unbox(x_115);
lean_dec(x_115);
x_188 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_113, x_12, x_118, x_11, x_187, x_177, x_117, x_186, x_2, x_3, x_4, x_5);
lean_dec_ref(x_11);
return x_188;
}
block_195:
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_192);
x_176 = x_190;
x_177 = x_191;
x_178 = x_194;
x_179 = lean_box(0);
goto block_189;
}
block_201:
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_198);
x_176 = x_196;
x_177 = x_197;
x_178 = x_200;
x_179 = lean_box(0);
goto block_189;
}
block_206:
{
lean_object* x_205; 
x_205 = lean_box(0);
x_196 = x_203;
x_197 = x_204;
x_198 = x_205;
x_199 = lean_box(0);
goto block_201;
}
block_229:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_nat_add(x_214, x_216);
lean_dec(x_216);
lean_dec(x_214);
x_222 = lean_box(x_207);
lean_inc(x_221);
x_223 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelow___lam__0___boxed), 15, 8);
lean_closure_set(x_223, 0, x_209);
lean_closure_set(x_223, 1, x_221);
lean_closure_set(x_223, 2, x_208);
lean_closure_set(x_223, 3, x_13);
lean_closure_set(x_223, 4, x_211);
lean_closure_set(x_223, 5, x_210);
lean_closure_set(x_223, 6, x_212);
lean_closure_set(x_223, 7, x_222);
x_224 = lean_nat_add(x_221, x_213);
lean_dec(x_213);
lean_dec(x_221);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_226 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(x_220, x_225, x_223, x_215, x_215, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_196 = x_217;
x_197 = x_219;
x_198 = x_227;
x_199 = lean_box(0);
goto block_201;
}
else
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec_ref(x_226);
x_190 = x_217;
x_191 = x_219;
x_192 = x_228;
x_193 = lean_box(0);
goto block_195;
}
}
block_255:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1));
x_236 = l_Lean_Name_append(x_1, x_235);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_237 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(x_236, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_238 = lean_ctor_get(x_232, 0);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec_ref(x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_232, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_232, 5);
lean_inc(x_242);
lean_dec_ref(x_232);
x_243 = lean_ctor_get(x_238, 1);
lean_inc(x_243);
lean_dec_ref(x_238);
x_244 = lean_ctor_get(x_239, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_239, 4);
lean_inc(x_245);
x_246 = lean_ctor_get(x_239, 5);
lean_inc(x_246);
lean_dec(x_239);
x_247 = lean_ctor_get(x_240, 1);
x_248 = lean_ctor_get(x_240, 2);
x_249 = l_List_lengthTR___redArg(x_243);
x_250 = l_List_lengthTR___redArg(x_247);
x_251 = lean_nat_dec_lt(x_249, x_250);
lean_dec(x_250);
lean_dec(x_249);
if (x_251 == 0)
{
lean_inc_ref(x_248);
lean_dec_ref(x_240);
lean_inc(x_244);
x_207 = x_251;
x_208 = x_241;
x_209 = x_244;
x_210 = x_242;
x_211 = x_235;
x_212 = x_243;
x_213 = x_246;
x_214 = x_244;
x_215 = x_234;
x_216 = x_245;
x_217 = x_231;
x_218 = lean_box(0);
x_219 = x_233;
x_220 = x_248;
goto block_229;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__0));
x_253 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_240, x_252);
lean_inc(x_244);
x_207 = x_251;
x_208 = x_241;
x_209 = x_244;
x_210 = x_242;
x_211 = x_235;
x_212 = x_243;
x_213 = x_246;
x_214 = x_244;
x_215 = x_234;
x_216 = x_245;
x_217 = x_231;
x_218 = lean_box(0);
x_219 = x_233;
x_220 = x_253;
goto block_229;
}
}
else
{
lean_object* x_254; 
lean_dec_ref(x_232);
x_254 = lean_ctor_get(x_237, 0);
lean_inc(x_254);
lean_dec_ref(x_237);
x_190 = x_231;
x_191 = x_233;
x_192 = x_254;
x_193 = lean_box(0);
goto block_195;
}
}
block_302:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(x_5);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_trace_profiler_useHeartbeats;
x_259 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_11, x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_io_mono_nanos_now();
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_261 = l_Lean_Meta_isInductivePredicate(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_unbox(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; 
lean_dec(x_1);
x_264 = lean_box(0);
x_136 = x_260;
x_137 = x_257;
x_138 = x_264;
x_139 = lean_box(0);
goto block_141;
}
else
{
lean_object* x_265; 
lean_inc(x_1);
x_265 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = lean_ctor_get_uint8(x_266, sizeof(void*)*6 + 1);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = lean_ctor_get_uint8(x_266, sizeof(void*)*6);
if (x_268 == 0)
{
lean_dec(x_266);
lean_dec(x_1);
x_142 = lean_box(0);
x_143 = x_260;
x_144 = x_257;
goto block_146;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_266, 0);
lean_inc_ref(x_269);
x_270 = lean_ctor_get(x_266, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 5);
lean_inc(x_271);
lean_dec(x_266);
x_272 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1));
x_273 = l_Lean_Name_append(x_1, x_272);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_274 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(x_273, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec_ref(x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_269, 1);
lean_inc(x_277);
lean_dec_ref(x_269);
x_278 = lean_ctor_get(x_275, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_275, 4);
lean_inc(x_279);
x_280 = lean_ctor_get(x_275, 5);
lean_inc(x_280);
lean_dec(x_275);
x_281 = lean_ctor_get(x_276, 1);
x_282 = lean_ctor_get(x_276, 2);
x_283 = l_List_lengthTR___redArg(x_277);
x_284 = l_List_lengthTR___redArg(x_281);
x_285 = lean_nat_dec_lt(x_283, x_284);
lean_dec(x_284);
lean_dec(x_283);
if (x_285 == 0)
{
lean_inc_ref(x_282);
lean_dec_ref(x_276);
lean_inc(x_278);
x_153 = x_285;
x_154 = x_270;
x_155 = x_278;
x_156 = x_272;
x_157 = x_271;
x_158 = x_277;
x_159 = x_280;
x_160 = x_278;
x_161 = lean_box(0);
x_162 = x_259;
x_163 = x_260;
x_164 = x_279;
x_165 = x_257;
x_166 = x_282;
goto block_175;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__0));
x_287 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_276, x_286);
lean_inc(x_278);
x_153 = x_285;
x_154 = x_270;
x_155 = x_278;
x_156 = x_272;
x_157 = x_271;
x_158 = x_277;
x_159 = x_280;
x_160 = x_278;
x_161 = lean_box(0);
x_162 = x_259;
x_163 = x_260;
x_164 = x_279;
x_165 = x_257;
x_166 = x_287;
goto block_175;
}
}
else
{
lean_object* x_288; 
lean_dec(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_116);
x_288 = lean_ctor_get(x_274, 0);
lean_inc(x_288);
lean_dec_ref(x_274);
x_147 = x_260;
x_148 = x_257;
x_149 = x_288;
x_150 = lean_box(0);
goto block_152;
}
}
}
else
{
lean_dec(x_266);
lean_dec(x_1);
x_142 = lean_box(0);
x_143 = x_260;
x_144 = x_257;
goto block_146;
}
}
else
{
lean_object* x_289; 
lean_dec(x_116);
lean_dec(x_1);
x_289 = lean_ctor_get(x_265, 0);
lean_inc(x_289);
lean_dec_ref(x_265);
x_147 = x_260;
x_148 = x_257;
x_149 = x_289;
x_150 = lean_box(0);
goto block_152;
}
}
}
else
{
lean_object* x_290; 
lean_dec(x_116);
lean_dec(x_1);
x_290 = lean_ctor_get(x_261, 0);
lean_inc(x_290);
lean_dec_ref(x_261);
x_147 = x_260;
x_148 = x_257;
x_149 = x_290;
x_150 = lean_box(0);
goto block_152;
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_116);
x_291 = lean_io_get_num_heartbeats();
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_292 = l_Lean_Meta_isInductivePredicate(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
x_294 = lean_unbox(x_293);
lean_dec(x_293);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_1);
x_295 = lean_box(0);
x_196 = x_291;
x_197 = x_257;
x_198 = x_295;
x_199 = lean_box(0);
goto block_201;
}
else
{
lean_object* x_296; 
lean_inc(x_1);
x_296 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_dec_ref(x_296);
x_298 = lean_ctor_get_uint8(x_297, sizeof(void*)*6 + 1);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_297, sizeof(void*)*6);
if (x_299 == 0)
{
if (x_259 == 0)
{
x_230 = lean_box(0);
x_231 = x_291;
x_232 = x_297;
x_233 = x_257;
x_234 = x_259;
goto block_255;
}
else
{
lean_dec(x_297);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = x_291;
x_204 = x_257;
goto block_206;
}
}
else
{
x_230 = lean_box(0);
x_231 = x_291;
x_232 = x_297;
x_233 = x_257;
x_234 = x_298;
goto block_255;
}
}
else
{
lean_dec(x_297);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = x_291;
x_204 = x_257;
goto block_206;
}
}
else
{
lean_object* x_300; 
lean_dec(x_1);
x_300 = lean_ctor_get(x_296, 0);
lean_inc(x_300);
lean_dec_ref(x_296);
x_190 = x_291;
x_191 = x_257;
x_192 = x_300;
x_193 = lean_box(0);
goto block_195;
}
}
}
else
{
lean_object* x_301; 
lean_dec(x_1);
x_301 = lean_ctor_get(x_292, 0);
lean_inc(x_301);
lean_dec_ref(x_292);
x_190 = x_291;
x_191 = x_257;
x_192 = x_301;
x_193 = lean_box(0);
goto block_195;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_36:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_nat_add(x_26, x_20);
lean_dec(x_20);
lean_dec(x_26);
x_31 = lean_box(x_14);
lean_inc(x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelow___lam__0___boxed), 15, 8);
lean_closure_set(x_32, 0, x_18);
lean_closure_set(x_32, 1, x_30);
lean_closure_set(x_32, 2, x_15);
lean_closure_set(x_32, 3, x_13);
lean_closure_set(x_32, 4, x_16);
lean_closure_set(x_32, 5, x_19);
lean_closure_set(x_32, 6, x_17);
lean_closure_set(x_32, 7, x_31);
x_33 = lean_nat_add(x_30, x_23);
lean_dec(x_23);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_IndPredBelow_mkBelow_spec__7___redArg(x_29, x_34, x_32, x_28, x_28, x_22, x_21, x_27, x_25);
return x_35;
}
block_112:
{
lean_object* x_42; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_1);
x_42 = l_Lean_Meta_isInductivePredicate(x_1, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; 
lean_free_object(x_42);
lean_inc(x_1);
x_47 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_1, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*6 + 1);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_48, sizeof(void*)*6);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 5);
lean_inc(x_53);
lean_dec(x_48);
x_54 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1));
x_55 = l_Lean_Name_append(x_1, x_54);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_56 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(x_55, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec_ref(x_51);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 5);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_58, 1);
x_64 = lean_ctor_get(x_58, 2);
x_65 = l_List_lengthTR___redArg(x_59);
x_66 = l_List_lengthTR___redArg(x_63);
x_67 = lean_nat_dec_lt(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_inc_ref(x_64);
lean_dec_ref(x_58);
lean_inc(x_60);
x_14 = x_67;
x_15 = x_52;
x_16 = x_54;
x_17 = x_59;
x_18 = x_60;
x_19 = x_53;
x_20 = x_61;
x_21 = x_38;
x_22 = x_37;
x_23 = x_62;
x_24 = lean_box(0);
x_25 = x_40;
x_26 = x_60;
x_27 = x_39;
x_28 = x_49;
x_29 = x_64;
goto block_36;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__0));
x_69 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_58, x_68);
lean_inc(x_60);
x_14 = x_67;
x_15 = x_52;
x_16 = x_54;
x_17 = x_59;
x_18 = x_60;
x_19 = x_53;
x_20 = x_61;
x_21 = x_38;
x_22 = x_37;
x_23 = x_62;
x_24 = lean_box(0);
x_25 = x_40;
x_26 = x_60;
x_27 = x_39;
x_28 = x_49;
x_29 = x_69;
goto block_36;
}
}
else
{
uint8_t x_70; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
lean_dec(x_56);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
uint8_t x_73; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_47);
if (x_73 == 0)
{
return x_47;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_47, 0);
lean_inc(x_74);
lean_dec(x_47);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_42, 0);
lean_inc(x_76);
lean_dec(x_42);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; 
lean_inc(x_1);
x_80 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_1, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*6 + 1);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_81, sizeof(void*)*6);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_81, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 5);
lean_inc(x_86);
lean_dec(x_81);
x_87 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__2___closed__1));
x_88 = l_Lean_Name_append(x_1, x_87);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_89 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1(x_88, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec_ref(x_84);
x_93 = lean_ctor_get(x_90, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 5);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_91, 1);
x_97 = lean_ctor_get(x_91, 2);
x_98 = l_List_lengthTR___redArg(x_92);
x_99 = l_List_lengthTR___redArg(x_96);
x_100 = lean_nat_dec_lt(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_inc_ref(x_97);
lean_dec_ref(x_91);
lean_inc(x_93);
x_14 = x_100;
x_15 = x_85;
x_16 = x_87;
x_17 = x_92;
x_18 = x_93;
x_19 = x_86;
x_20 = x_94;
x_21 = x_38;
x_22 = x_37;
x_23 = x_95;
x_24 = lean_box(0);
x_25 = x_40;
x_26 = x_93;
x_27 = x_39;
x_28 = x_82;
x_29 = x_97;
goto block_36;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__0));
x_102 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_91, x_101);
lean_inc(x_93);
x_14 = x_100;
x_15 = x_85;
x_16 = x_87;
x_17 = x_92;
x_18 = x_93;
x_19 = x_86;
x_20 = x_94;
x_21 = x_38;
x_22 = x_37;
x_23 = x_95;
x_24 = lean_box(0);
x_25 = x_40;
x_26 = x_93;
x_27 = x_39;
x_28 = x_82;
x_29 = x_102;
goto block_36;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_104 = x_89;
} else {
 lean_dec_ref(x_89);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_106 = lean_ctor_get(x_80, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_107 = x_80;
} else {
 lean_dec_ref(x_80);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_42);
if (x_109 == 0)
{
return x_42;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_42, 0);
lean_inc(x_110);
lean_dec(x_42);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_IndPredBelow_mkBelow(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findIdx_x3f_loop___redArg(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_array_get_size(x_2);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
x_8 = lean_expr_eqv(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0_spec__2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_15 = lean_infer_type(x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_22 = l_Lean_Expr_getForallBody(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Expr_getAppFn(x_24);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = l_Lean_Expr_getAppFn(x_23);
lean_dec_ref(x_23);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = l_Array_idxOf_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__0(x_1, x_26);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Array_idxOf___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__1(x_25, x_2);
x_30 = lean_nat_sub(x_29, x_3);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_7, x_31);
x_17 = x_32;
goto block_21;
}
else
{
lean_dec(x_27);
lean_dec_ref(x_25);
x_17 = x_7;
goto block_21;
}
}
else
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_17 = x_7;
goto block_21;
}
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
x_17 = x_7;
goto block_21;
}
}
else
{
lean_dec_ref(x_22);
x_17 = x_7;
goto block_21;
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_7 = x_17;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_7);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0;
x_13 = lean_nat_dec_lt(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_le(x_6, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_5, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_5);
x_20 = lean_usize_of_nat(x_15);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3(x_1, x_2, x_3, x_4, x_19, x_20, x_12, x_7, x_8, x_9, x_10);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_5);
x_23 = lean_usize_of_nat(x_6);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2_spec__3(x_1, x_2, x_3, x_4, x_22, x_23, x_12, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_10 = l_Array_extract___redArg(x_3, x_1, x_2);
x_11 = lean_array_get_size(x_3);
x_12 = l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2(x_10, x_3, x_2, x_3, x_2, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec_ref(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___lam__0___boxed), 9, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_9);
x_12 = 0;
x_13 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_10, x_11, x_12, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Expr_fvar___override(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Lean_Expr_fvar___override(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_MessageData_ofExpr(x_5);
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
x_11 = l_Lean_MessageData_ofName(x_6);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_MessageData_ofExpr(x_7);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_paren(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_paren(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = l_Lean_MessageData_ofExpr(x_19);
x_23 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_24);
x_26 = l_Lean_MessageData_ofName(x_20);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = l_Lean_MessageData_ofExpr(x_21);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_paren(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_paren(x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_39 = l_Lean_MessageData_ofExpr(x_35);
x_40 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(7, 2, 0);
} else {
 x_41 = x_38;
 lean_ctor_set_tag(x_41, 7);
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofName(x_36);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = l_Lean_MessageData_ofExpr(x_37);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_MessageData_paren(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_MessageData_paren(x_50);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__4(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Expr_fvar___override(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Lean_Expr_fvar___override(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__5(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_MessageData_ofExpr(x_5);
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
x_11 = l_Nat_reprFast(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = l_Lean_MessageData_ofExpr(x_7);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_paren(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_paren(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = l_Lean_MessageData_ofExpr(x_21);
x_25 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_26);
x_28 = l_Nat_reprFast(x_22);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = l_Lean_MessageData_ofExpr(x_23);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_MessageData_paren(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_paren(x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = l_Lean_MessageData_ofExpr(x_39);
x_44 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(7, 2, 0);
} else {
 x_45 = x_42;
 lean_ctor_set_tag(x_45, 7);
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Nat_reprFast(x_40);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = l_Lean_MessageData_ofExpr(x_41);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_MessageData_paren(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_paren(x_56);
return x_57;
}
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__15));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2;
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3;
x_13 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_1, x_12, x_9);
x_14 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13));
x_15 = lean_array_size(x_13);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_14, x_2, x_15, x_16, x_13);
x_18 = lean_array_to_list(x_17);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___redArg(x_3, x_18, x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_11);
x_22 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_4, x_12, x_10);
x_25 = lean_array_size(x_24);
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_14, x_5, x_25, x_16, x_24);
x_27 = lean_array_to_list(x_26);
x_28 = l_List_mapTR_loop___redArg(x_6, x_27, x_19);
x_29 = l_Lean_MessageData_ofList(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2;
x_34 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3;
x_35 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_1, x_34, x_31);
x_36 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13));
x_37 = lean_array_size(x_35);
x_38 = 0;
x_39 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_36, x_2, x_37, x_38, x_35);
x_40 = lean_array_to_list(x_39);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___redArg(x_3, x_40, x_41);
x_43 = l_Lean_MessageData_ofList(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_4, x_34, x_32);
x_48 = lean_array_size(x_47);
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_36, x_5, x_48, x_38, x_47);
x_50 = lean_array_to_list(x_49);
x_51 = l_List_mapTR_loop___redArg(x_6, x_50, x_41);
x_52 = l_Lean_MessageData_ofList(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_below_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_below_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_motive_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_motive_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1;
x_8 = l_Lean_LocalDecl_toExpr(x_4);
x_9 = l_Lean_MessageData_ofExpr(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_ofName(x_5);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13));
x_17 = lean_array_size(x_6);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_16, x_1, x_17, x_18, x_6);
x_20 = lean_array_to_list(x_19);
x_21 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__4));
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___redArg(x_21, x_20, x_22);
x_24 = l_Lean_MessageData_ofList(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_3);
x_29 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6;
x_30 = l_Lean_LocalDecl_toExpr(x_26);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Nat_reprFast(x_27);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
x_40 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__13));
x_41 = lean_array_size(x_28);
x_42 = 0;
x_43 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_40, x_2, x_41, x_42, x_28);
x_44 = lean_array_to_list(x_43);
x_45 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__4));
x_46 = lean_box(0);
x_47 = l_List_mapTR_loop___redArg(x_45, x_44, x_46);
x_48 = l_Lean_MessageData_ofList(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__0));
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_getDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_getDecl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_NewDecl_getDecl(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_array_push(x_2, x_5);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0;
x_3 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_6);
x_16 = lean_array_set(x_7, x_8, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
lean_dec(x_8);
x_6 = x_14;
x_7 = x_16;
x_8 = x_18;
goto _start;
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_5);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec_ref(x_6);
x_22 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_20, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Expr_const___override(x_1, x_21);
x_26 = l_Lean_mkAppN(x_25, x_2);
x_27 = lean_array_get_size(x_7);
x_28 = l_Array_extract___redArg(x_7, x_24, x_27);
lean_dec_ref(x_7);
x_29 = l_Lean_mkAppN(x_26, x_28);
lean_dec_ref(x_28);
x_30 = l_Lean_mkAppN(x_3, x_4);
x_31 = l_Lean_Expr_app___override(x_29, x_30);
x_32 = 0;
x_33 = 1;
x_34 = 1;
x_35 = l_Lean_Meta_mkForallFVars(x_4, x_31, x_32, x_33, x_33, x_34, x_9, x_10, x_11, x_12);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
x_39 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1;
x_40 = l_Lean_MessageData_ofExpr(x_5);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_41, x_9, x_10, x_11, x_12);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
x_13 = l_Lean_Expr_getAppNumArgs(x_6);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
x_17 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0(x_1, x_2, x_3, x_5, x_4, x_6, x_14, x_16, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___boxed), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_10);
x_12 = 0;
x_13 = 1;
x_14 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__1___redArg(x_10, x_11, x_12, x_13, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_11, x_12, x_1, x_10, x_3, x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
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
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Nat_reprFast(x_8);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_12);
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Nat_reprFast(x_9);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_paren(x_19);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_20);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = l_Nat_reprFast(x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Nat_reprFast(x_24);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_MessageData_paren(x_35);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_36);
{
lean_object* _tmp_0 = x_22;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = l_Nat_reprFast(x_40);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2;
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(7, 2, 0);
} else {
 x_47 = x_42;
 lean_ctor_set_tag(x_47, 7);
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Nat_reprFast(x_41);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_paren(x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_2);
x_1 = x_39;
x_2 = x_55;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = l_Lean_Meta_Match_Pattern_toExpr(x_11, x_12, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_16, x_2, x_14);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_12, x_5, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
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
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_5);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg(x_1, x_12, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = 0;
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg(x_1, x_10, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0;
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_20 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_38 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
lean_inc_ref(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
x_46 = lean_box(0);
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_55 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
lean_inc_ref(x_50);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_62);
x_63 = l_ReaderT_instMonad___redArg(x_27);
x_64 = lean_box(0);
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_75 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
lean_inc_ref(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = lean_box(0);
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_94 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
lean_inc_ref(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_111 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
lean_inc_ref(x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_108);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_116, 0, x_107);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_117, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_115);
if (lean_is_scalar(x_104)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_104;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = l_ReaderT_instMonad___redArg(x_119);
x_121 = lean_box(0);
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__1));
x_132 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__2));
lean_inc_ref(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__3));
x_150 = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__4));
lean_inc_ref(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = lean_box(0);
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_163;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(121u);
x_4 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__2));
x_5 = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_st_ref_get(x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_1);
x_20 = l_Lean_Environment_findAsync_x3f(x_18, x_1, x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
if (x_22 == 6)
{
lean_object* x_23; 
x_23 = l_Lean_AsyncConstantInfo_toConstantInfo(x_21);
if (lean_obj_tag(x_23) == 6)
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_23);
x_27 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_28 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__1(x_27, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_free_object(x_28);
x_8 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
if (lean_obj_tag(x_32) == 0)
{
x_8 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_2);
x_8 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_20);
lean_dec(x_2);
x_8 = lean_box(0);
goto block_16;
}
block_16:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1;
x_10 = 0;
x_11 = l_Lean_MessageData_ofConstName(x_1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Meta_Match_Pattern_toExpr(x_1, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_exceptEmoji___redArg(x_3);
x_15 = l_Lean_stringToMessageData(x_14);
x_16 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofName(x_2);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = l_Lean_exceptEmoji___redArg(x_3);
x_26 = l_Lean_stringToMessageData(x_25);
x_27 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_24);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofName(x_2);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getFVarLocalDecl___redArg(x_3, x_5, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_st_ref_take(x_4);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_array_push(x_13, x_15);
x_17 = lean_st_ref_set(x_4, x_16);
x_18 = l_Lean_Expr_fvarId_x21(x_3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_st_ref_take(x_4);
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_st_ref_set(x_4, x_25);
x_27 = l_Lean_Expr_fvarId_x21(x_3);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_4, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = l_Lean_Meta_Match_Pattern_toExpr(x_12, x_1, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_st_ref_get(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_replaceRef(x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_20, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_st_ref_take(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Lean_PersistentArray_push___redArg(x_1, x_29);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_8, x_24);
x_32 = lean_box(0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_23);
x_35 = l_Lean_PersistentArray_push___redArg(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_33);
lean_ctor_set(x_24, 4, x_36);
x_37 = lean_st_ref_set(x_8, x_24);
x_38 = lean_box(0);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 5);
x_45 = lean_ctor_get(x_24, 6);
x_46 = lean_ctor_get(x_24, 7);
x_47 = lean_ctor_get(x_24, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_48 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_23);
x_51 = l_Lean_PersistentArray_push___redArg(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 8);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint64(x_52, sizeof(void*)*1, x_48);
x_53 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_44);
lean_ctor_set(x_53, 6, x_45);
lean_ctor_set(x_53, 7, x_46);
lean_ctor_set(x_53, 8, x_47);
x_54 = lean_st_ref_set(x_8, x_53);
x_55 = lean_box(0);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
lean_dec(x_21);
x_57 = lean_st_ref_take(x_8);
x_58 = lean_ctor_get(x_57, 4);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_57, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_57, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_57, 8);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get_uint64(x_58, sizeof(void*)*1);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_56);
x_71 = l_Lean_PersistentArray_push___redArg(x_1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 9, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_63);
lean_ctor_set(x_73, 6, x_64);
lean_ctor_set(x_73, 7, x_65);
lean_ctor_set(x_73, 8, x_66);
x_74 = lean_st_ref_set(x_8, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
x_79 = lean_ctor_get(x_7, 2);
x_80 = lean_ctor_get(x_7, 3);
x_81 = lean_ctor_get(x_7, 4);
x_82 = lean_ctor_get(x_7, 5);
x_83 = lean_ctor_get(x_7, 6);
x_84 = lean_ctor_get(x_7, 7);
x_85 = lean_ctor_get(x_7, 8);
x_86 = lean_ctor_get(x_7, 9);
x_87 = lean_ctor_get(x_7, 10);
x_88 = lean_ctor_get(x_7, 11);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_90 = lean_ctor_get(x_7, 12);
x_91 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_92 = lean_ctor_get(x_7, 13);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_93 = lean_st_ref_get(x_8);
x_94 = lean_ctor_get(x_93, 4);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_replaceRef(x_3, x_82);
lean_dec(x_82);
x_97 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
lean_ctor_set(x_97, 9, x_86);
lean_ctor_set(x_97, 10, x_87);
lean_ctor_set(x_97, 11, x_88);
lean_ctor_set(x_97, 12, x_90);
lean_ctor_set(x_97, 13, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*14, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*14 + 1, x_91);
x_98 = l_Lean_PersistentArray_toArray___redArg(x_95);
lean_dec_ref(x_95);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__13_spec__15(x_99, x_100, x_98);
x_102 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_4);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_102, x_5, x_6, x_97, x_8);
lean_dec_ref(x_97);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_st_ref_take(x_8);
x_107 = lean_ctor_get(x_106, 4);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_106, 5);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_106, 6);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_106, 7);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_106, 8);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get_uint64(x_107, sizeof(void*)*1);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_104);
x_120 = l_Lean_PersistentArray_push___redArg(x_1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint64(x_121, sizeof(void*)*1, x_117);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_109);
lean_ctor_set(x_122, 2, x_110);
lean_ctor_set(x_122, 3, x_111);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_112);
lean_ctor_set(x_122, 6, x_113);
lean_ctor_set(x_122, 7, x_114);
lean_ctor_set(x_122, 8, x_115);
x_123 = lean_st_ref_set(x_8, x_122);
x_124 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_105;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_50; double x_83; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec_ref(x_8);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = l_Lean_trace_profiler;
x_35 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_4, x_34);
if (x_35 == 0)
{
x_50 = x_35;
goto block_82;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_trace_profiler_useHeartbeats;
x_90 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_4, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; double x_93; double x_94; double x_95; 
x_91 = l_Lean_trace_profiler_threshold;
x_92 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(x_4, x_91);
x_93 = lean_float_of_nat(x_92);
x_94 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3;
x_95 = lean_float_div(x_93, x_94);
x_83 = x_95;
goto block_88;
}
else
{
lean_object* x_96; lean_object* x_97; double x_98; 
x_96 = l_Lean_trace_profiler_threshold;
x_97 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11_spec__15(x_4, x_96);
x_98 = lean_float_of_nat(x_97);
x_83 = x_98;
goto block_88;
}
}
block_31:
{
lean_object* x_26; 
lean_dec(x_20);
x_26 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg(x_6, x_19, x_17, x_18, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_15);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
block_44:
{
double x_39; lean_object* x_40; 
x_39 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
lean_inc_ref(x_3);
lean_inc(x_1);
x_40 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set_float(x_40, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_40, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 16, x_2);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_3);
lean_dec(x_1);
x_17 = x_36;
x_18 = x_37;
x_19 = x_40;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_41; double x_42; double x_43; 
lean_dec_ref(x_40);
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_3);
x_42 = lean_unbox_float(x_32);
lean_dec(x_32);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_42);
x_43 = lean_unbox_float(x_33);
lean_dec(x_33);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_2);
x_17 = x_36;
x_18 = x_37;
x_19 = x_41;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = lean_box(0);
goto block_31;
}
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_12, 5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_46 = lean_apply_7(x_7, x_15, x_9, x_10, x_11, x_12, x_13, lean_box(0));
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc(x_45);
x_36 = x_45;
x_37 = x_47;
x_38 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_48; 
lean_dec_ref(x_46);
x_48 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2;
lean_inc(x_45);
x_36 = x_45;
x_37 = x_48;
x_38 = lean_box(0);
goto block_44;
}
}
block_82:
{
if (x_5 == 0)
{
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = lean_st_ref_take(x_13);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 4);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l_Lean_PersistentArray_append___redArg(x_6, x_55);
lean_dec_ref(x_55);
lean_ctor_set(x_53, 0, x_56);
x_57 = lean_st_ref_set(x_13, x_51);
lean_dec(x_13);
x_58 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_15);
return x_58;
}
else
{
uint64_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get_uint64(x_53, sizeof(void*)*1);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec(x_53);
x_61 = l_Lean_PersistentArray_append___redArg(x_6, x_60);
lean_dec_ref(x_60);
x_62 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint64(x_62, sizeof(void*)*1, x_59);
lean_ctor_set(x_51, 4, x_62);
x_63 = lean_st_ref_set(x_13, x_51);
lean_dec(x_13);
x_64 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_15);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_65 = lean_ctor_get(x_51, 4);
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get(x_51, 1);
x_68 = lean_ctor_get(x_51, 2);
x_69 = lean_ctor_get(x_51, 3);
x_70 = lean_ctor_get(x_51, 5);
x_71 = lean_ctor_get(x_51, 6);
x_72 = lean_ctor_get(x_51, 7);
x_73 = lean_ctor_get(x_51, 8);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_65);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_74 = lean_ctor_get_uint64(x_65, sizeof(void*)*1);
x_75 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_76 = x_65;
} else {
 lean_dec_ref(x_65);
 x_76 = lean_box(0);
}
x_77 = l_Lean_PersistentArray_append___redArg(x_6, x_75);
lean_dec_ref(x_75);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 1, 8);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_uint64(x_78, sizeof(void*)*1, x_74);
x_79 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_67);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_69);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_70);
lean_ctor_set(x_79, 6, x_71);
lean_ctor_set(x_79, 7, x_72);
lean_ctor_set(x_79, 8, x_73);
x_80 = lean_st_ref_set(x_13, x_79);
lean_dec(x_13);
x_81 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_15);
return x_81;
}
}
else
{
goto block_49;
}
}
else
{
goto block_49;
}
}
block_88:
{
double x_84; double x_85; double x_86; uint8_t x_87; 
x_84 = lean_unbox_float(x_33);
x_85 = lean_unbox_float(x_32);
x_86 = lean_float_sub(x_84, x_85);
x_87 = lean_float_decLt(x_83, x_86);
x_50 = x_87;
goto block_82;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_5);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(x_1, x_15, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_st_ref_get(x_10);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_3);
x_19 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4(x_8, x_2, x_3, x_4, x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = 0;
x_25 = l_Lean_Meta_Match_Pattern_toExpr(x_5, x_24, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_array_to_list(x_3);
x_30 = lean_array_to_list(x_22);
lean_inc(x_28);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_20, 1, x_31);
lean_ctor_set(x_20, 0, x_32);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_array_to_list(x_3);
x_36 = lean_array_to_list(x_22);
lean_inc(x_34);
x_37 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_7);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_20, 1, x_37);
lean_ctor_set(x_20, 0, x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_20);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_7);
lean_dec_ref(x_3);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
lean_dec(x_20);
x_44 = 0;
x_45 = l_Lean_Meta_Match_Pattern_toExpr(x_5, x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_array_to_list(x_3);
x_50 = lean_array_to_list(x_43);
lean_inc(x_48);
x_51 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_7);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_46);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_7);
lean_dec_ref(x_3);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
return x_19;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_19, 0);
lean_inc(x_59);
lean_dec(x_19);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_19 = l_Lean_Meta_instantiateForall(x_1, x_2, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_21 = l_Lean_Meta_instantiateForall(x_20, x_3, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(x_4, x_5, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_6);
x_25 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_6, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_box(x_9);
lean_inc_ref(x_10);
lean_inc(x_24);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2___boxed), 16, 8);
lean_closure_set(x_28, 0, x_7);
lean_closure_set(x_28, 1, x_24);
lean_closure_set(x_28, 2, x_2);
lean_closure_set(x_28, 3, x_5);
lean_closure_set(x_28, 4, x_8);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_10);
lean_closure_set(x_28, 7, x_11);
x_29 = lean_unbox(x_26);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec_ref(x_10);
lean_dec(x_6);
x_30 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_22, x_28, x_9, x_13, x_14, x_15, x_16, x_17);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec_ref(x_10);
x_32 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1;
x_33 = l_Lean_MessageData_ofConstName(x_31, x_9);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_to_list(x_24);
x_38 = lean_box(0);
x_39 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__6(x_37, x_38);
x_40 = l_Lean_MessageData_ofList(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_6, x_41, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec_ref(x_42);
x_43 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_22, x_28, x_9, x_13, x_14, x_15, x_16, x_17);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_25, 0);
lean_inc(x_48);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_21, 0);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_19, 0);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_18 = l_Lean_Meta_instantiateForall(x_1, x_2, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_20 = l_Lean_Meta_instantiateForall(x_19, x_3, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_5);
x_22 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(x_4, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_6);
x_24 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_6, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_36; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc_ref(x_9);
lean_inc(x_23);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0___boxed), 15, 7);
lean_closure_set(x_26, 0, x_7);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_5);
lean_closure_set(x_26, 4, x_8);
lean_closure_set(x_26, 5, x_9);
lean_closure_set(x_26, 6, x_10);
x_36 = lean_unbox(x_25);
lean_dec(x_25);
if (x_36 == 0)
{
lean_dec(x_23);
lean_dec_ref(x_9);
lean_dec(x_6);
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec_ref(x_9);
x_38 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1;
x_39 = 0;
x_40 = l_Lean_MessageData_ofConstName(x_37, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_to_list(x_23);
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__6(x_44, x_45);
x_47 = l_Lean_MessageData_ofList(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_6, x_48, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_50; 
lean_dec_ref(x_26);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
block_35:
{
uint8_t x_33; lean_object* x_34; 
x_33 = 0;
x_34 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_21, x_26, x_33, x_27, x_28, x_29, x_30, x_31);
return x_34;
}
}
else
{
uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_24, 0);
lean_inc(x_54);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_22, 0);
lean_inc(x_57);
lean_dec(x_22);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_59 = !lean_is_exclusive(x_20);
if (x_59 == 0)
{
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_18);
if (x_62 == 0)
{
return x_18;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_18, 0);
lean_inc(x_63);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
switch (lean_obj_tag(x_4)) {
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_5);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 3);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_28 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
if (x_27 == 0)
{
lean_object* x_134; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_134 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_79 = x_135;
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = lean_box(0);
goto block_133;
}
else
{
uint8_t x_136; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
return x_134;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; 
x_139 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_28, x_9);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_304; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
lean_inc(x_3);
lean_inc_ref(x_4);
x_141 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___boxed), 9, 2);
lean_closure_set(x_141, 0, x_4);
lean_closure_set(x_141, 1, x_3);
x_142 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_304 = lean_unbox(x_140);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = l_Lean_trace_profiler;
x_306 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_23, x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec_ref(x_141);
lean_dec(x_140);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_307 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
x_79 = x_308;
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = lean_box(0);
goto block_133;
}
else
{
uint8_t x_309; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_309 = !lean_is_exclusive(x_307);
if (x_309 == 0)
{
return x_307;
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
}
}
else
{
lean_inc_ref(x_23);
goto block_303;
}
}
else
{
lean_inc_ref(x_23);
goto block_303;
}
block_156:
{
lean_object* x_147; double x_148; double x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_147 = lean_io_get_num_heartbeats();
x_148 = lean_float_of_nat(x_143);
x_149 = lean_float_of_nat(x_147);
x_150 = lean_box_float(x_148);
x_151 = lean_box_float(x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_unbox(x_140);
lean_dec(x_140);
x_155 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(x_28, x_27, x_142, x_23, x_154, x_144, x_141, x_153, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_155;
}
block_162:
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_159);
x_143 = x_157;
x_144 = x_158;
x_145 = x_161;
x_146 = lean_box(0);
goto block_156;
}
block_170:
{
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_ctor_set_tag(x_165, 1);
x_143 = x_163;
x_144 = x_164;
x_145 = x_165;
x_146 = lean_box(0);
goto block_156;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_143 = x_163;
x_144 = x_164;
x_145 = x_168;
x_146 = lean_box(0);
goto block_156;
}
}
else
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
lean_dec_ref(x_165);
x_157 = x_163;
x_158 = x_164;
x_159 = x_169;
x_160 = lean_box(0);
goto block_162;
}
}
block_187:
{
lean_object* x_175; double x_176; double x_177; double x_178; double x_179; double x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_175 = lean_io_mono_nanos_now();
x_176 = lean_float_of_nat(x_171);
x_177 = l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
x_178 = lean_float_div(x_176, x_177);
x_179 = lean_float_of_nat(x_175);
x_180 = lean_float_div(x_179, x_177);
x_181 = lean_box_float(x_178);
x_182 = lean_box_float(x_180);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_unbox(x_140);
lean_dec(x_140);
x_186 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(x_28, x_27, x_142, x_23, x_185, x_172, x_141, x_184, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_186;
}
block_193:
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_190);
x_171 = x_188;
x_172 = x_189;
x_173 = x_192;
x_174 = lean_box(0);
goto block_187;
}
block_201:
{
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_ctor_set_tag(x_196, 1);
x_171 = x_194;
x_172 = x_195;
x_173 = x_196;
x_174 = lean_box(0);
goto block_187;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_171 = x_194;
x_172 = x_195;
x_173 = x_199;
x_174 = lean_box(0);
goto block_187;
}
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
lean_dec_ref(x_196);
x_188 = x_194;
x_189 = x_195;
x_190 = x_200;
x_191 = lean_box(0);
goto block_193;
}
}
block_303:
{
lean_object* x_202; 
x_202 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__8___redArg(x_10);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = l_Lean_trace_profiler_useHeartbeats;
x_205 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_23, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_io_mono_nanos_now();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_207 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_box(0);
lean_inc(x_24);
x_211 = l_Lean_Name_replacePrefix(x_24, x_209, x_210);
lean_dec(x_209);
x_212 = l_Lean_Name_append(x_3, x_211);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_213 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_212, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
lean_inc(x_26);
x_215 = lean_array_mk(x_26);
x_216 = lean_array_size(x_215);
x_217 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_215);
x_218 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg(x_205, x_216, x_217, x_215, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_28, x_9);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get(x_214, 0);
lean_inc_ref(x_222);
lean_inc(x_25);
lean_inc_ref(x_222);
x_223 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_222, x_25);
x_224 = lean_unbox(x_221);
lean_dec(x_221);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_226 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3(x_223, x_1, x_219, x_214, x_2, x_28, x_215, x_4, x_205, x_222, x_25, x_225, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_219);
x_194 = x_206;
x_195 = x_203;
x_196 = x_226;
goto block_201;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_227 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
lean_inc_ref(x_223);
x_228 = l_Lean_MessageData_ofExpr(x_223);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
lean_inc_ref(x_1);
x_232 = lean_array_to_list(x_1);
x_233 = lean_box(0);
x_234 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_232, x_233);
x_235 = l_Lean_MessageData_ofList(x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_235);
x_237 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_219);
x_239 = lean_array_to_list(x_219);
x_240 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_239, x_233);
x_241 = l_Lean_MessageData_ofList(x_240);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_241);
x_243 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_28, x_244, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_247 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3(x_223, x_1, x_219, x_214, x_2, x_28, x_215, x_4, x_205, x_222, x_25, x_246, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_219);
x_194 = x_206;
x_195 = x_203;
x_196 = x_247;
goto block_201;
}
else
{
lean_object* x_248; 
lean_dec_ref(x_223);
lean_dec_ref(x_222);
lean_dec(x_219);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
lean_dec_ref(x_245);
x_188 = x_206;
x_189 = x_203;
x_190 = x_248;
x_191 = lean_box(0);
goto block_193;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_219);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_249 = lean_ctor_get(x_220, 0);
lean_inc(x_249);
lean_dec_ref(x_220);
x_188 = x_206;
x_189 = x_203;
x_190 = x_249;
x_191 = lean_box(0);
goto block_193;
}
}
else
{
lean_object* x_250; 
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_218, 0);
lean_inc(x_250);
lean_dec_ref(x_218);
x_188 = x_206;
x_189 = x_203;
x_190 = x_250;
x_191 = lean_box(0);
goto block_193;
}
}
else
{
lean_object* x_251; 
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_251 = lean_ctor_get(x_213, 0);
lean_inc(x_251);
lean_dec_ref(x_213);
x_188 = x_206;
x_189 = x_203;
x_190 = x_251;
x_191 = lean_box(0);
goto block_193;
}
}
else
{
lean_object* x_252; 
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_252 = lean_ctor_get(x_207, 0);
lean_inc(x_252);
lean_dec_ref(x_207);
x_188 = x_206;
x_189 = x_203;
x_190 = x_252;
x_191 = lean_box(0);
goto block_193;
}
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_io_get_num_heartbeats();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_254 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_box(0);
lean_inc(x_24);
x_258 = l_Lean_Name_replacePrefix(x_24, x_256, x_257);
lean_dec(x_256);
x_259 = l_Lean_Name_append(x_3, x_258);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_260 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_259, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; size_t x_263; size_t x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec_ref(x_260);
lean_inc(x_26);
x_262 = lean_array_mk(x_26);
x_263 = lean_array_size(x_262);
x_264 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_262);
x_265 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(x_263, x_264, x_262, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_28, x_9);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = lean_ctor_get(x_261, 0);
lean_inc_ref(x_269);
lean_inc(x_25);
lean_inc_ref(x_269);
x_270 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_269, x_25);
x_271 = lean_unbox(x_268);
lean_dec(x_268);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_273 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5(x_270, x_1, x_266, x_261, x_2, x_28, x_262, x_4, x_269, x_25, x_272, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_266);
x_163 = x_253;
x_164 = x_203;
x_165 = x_273;
goto block_170;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_274 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
lean_inc_ref(x_270);
x_275 = l_Lean_MessageData_ofExpr(x_270);
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
lean_inc_ref(x_1);
x_279 = lean_array_to_list(x_1);
x_280 = lean_box(0);
x_281 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_279, x_280);
x_282 = l_Lean_MessageData_ofList(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_282);
x_284 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
lean_inc(x_266);
x_286 = lean_array_to_list(x_266);
x_287 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_286, x_280);
x_288 = l_Lean_MessageData_ofList(x_287);
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_288);
x_290 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
x_291 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_28, x_291, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_294 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5(x_270, x_1, x_266, x_261, x_2, x_28, x_262, x_4, x_269, x_25, x_293, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_266);
x_163 = x_253;
x_164 = x_203;
x_165 = x_294;
goto block_170;
}
else
{
lean_object* x_295; 
lean_dec_ref(x_270);
lean_dec_ref(x_269);
lean_dec(x_266);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
lean_dec_ref(x_292);
x_157 = x_253;
x_158 = x_203;
x_159 = x_295;
x_160 = lean_box(0);
goto block_162;
}
}
}
else
{
lean_object* x_296; 
lean_dec(x_266);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_296 = lean_ctor_get(x_267, 0);
lean_inc(x_296);
lean_dec_ref(x_267);
x_157 = x_253;
x_158 = x_203;
x_159 = x_296;
x_160 = lean_box(0);
goto block_162;
}
}
else
{
lean_object* x_297; 
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_297 = lean_ctor_get(x_265, 0);
lean_inc(x_297);
lean_dec_ref(x_265);
x_157 = x_253;
x_158 = x_203;
x_159 = x_297;
x_160 = lean_box(0);
goto block_162;
}
}
else
{
lean_object* x_298; 
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_260, 0);
lean_inc(x_298);
lean_dec_ref(x_260);
x_157 = x_253;
x_158 = x_203;
x_159 = x_298;
x_160 = lean_box(0);
goto block_162;
}
}
else
{
lean_object* x_299; 
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_299 = lean_ctor_get(x_254, 0);
lean_inc(x_299);
lean_dec_ref(x_254);
x_157 = x_253;
x_158 = x_203;
x_159 = x_299;
x_160 = lean_box(0);
goto block_162;
}
}
}
else
{
uint8_t x_300; 
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_300 = !lean_is_exclusive(x_202);
if (x_300 == 0)
{
return x_202;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_202, 0);
lean_inc(x_301);
lean_dec(x_202);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_312 = !lean_is_exclusive(x_139);
if (x_312 == 0)
{
return x_139;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_139, 0);
lean_inc(x_313);
lean_dec(x_139);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
}
block_78:
{
lean_object* x_40; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
x_40 = l_Lean_Meta_instantiateForall(x_31, x_1, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
x_42 = l_Lean_Meta_instantiateForall(x_41, x_32, x_35, x_36, x_37, x_38);
lean_dec_ref(x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_2);
x_44 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices(x_33, x_2, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_28, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc_ref(x_29);
lean_inc(x_45);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__0___boxed), 15, 7);
lean_closure_set(x_48, 0, x_30);
lean_closure_set(x_48, 1, x_45);
lean_closure_set(x_48, 2, x_1);
lean_closure_set(x_48, 3, x_2);
lean_closure_set(x_48, 4, x_4);
lean_closure_set(x_48, 5, x_29);
lean_closure_set(x_48, 6, x_25);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_dec(x_45);
lean_dec_ref(x_29);
x_12 = x_43;
x_13 = x_48;
x_14 = x_34;
x_15 = x_35;
x_16 = x_36;
x_17 = x_37;
x_18 = x_38;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_29, 0);
lean_inc(x_50);
lean_dec_ref(x_29);
x_51 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1;
x_52 = 0;
x_53 = l_Lean_MessageData_ofConstName(x_50, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_to_list(x_45);
x_58 = lean_box(0);
x_59 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__6(x_57, x_58);
x_60 = l_Lean_MessageData_ofList(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_28, x_61, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_12 = x_43;
x_13 = x_48;
x_14 = x_34;
x_15 = x_35;
x_16 = x_36;
x_17 = x_37;
x_18 = x_38;
x_19 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_63; 
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_46);
if (x_66 == 0)
{
return x_46;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_46, 0);
lean_inc(x_67);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_43);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_44);
if (x_69 == 0)
{
return x_44;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_44, 0);
lean_inc(x_70);
lean_dec(x_44);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
lean_dec(x_42);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
lean_dec(x_40);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
block_133:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec_ref(x_79);
x_87 = lean_box(0);
lean_inc(x_24);
x_88 = l_Lean_Name_replacePrefix(x_24, x_86, x_87);
lean_dec(x_86);
x_89 = l_Lean_Name_append(x_3, x_88);
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc(x_80);
x_90 = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0(x_89, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
lean_inc(x_26);
x_92 = lean_array_mk(x_26);
x_93 = lean_array_size(x_92);
x_94 = 0;
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc_ref(x_92);
x_95 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(x_93, x_94, x_92, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_28, x_83);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_99);
lean_inc(x_25);
lean_inc_ref(x_99);
x_100 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_99, x_25);
x_101 = lean_unbox(x_98);
lean_dec(x_98);
if (x_101 == 0)
{
x_29 = x_99;
x_30 = x_92;
x_31 = x_100;
x_32 = x_96;
x_33 = x_91;
x_34 = x_80;
x_35 = x_81;
x_36 = x_82;
x_37 = x_83;
x_38 = x_84;
x_39 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_102 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
lean_inc_ref(x_100);
x_103 = l_Lean_MessageData_ofExpr(x_100);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc_ref(x_1);
x_107 = lean_array_to_list(x_1);
x_108 = lean_box(0);
x_109 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_107, x_108);
x_110 = l_Lean_MessageData_ofList(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_96);
x_114 = lean_array_to_list(x_96);
x_115 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_114, x_108);
x_116 = l_Lean_MessageData_ofList(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_28, x_119, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_120) == 0)
{
lean_dec_ref(x_120);
x_29 = x_99;
x_30 = x_92;
x_31 = x_100;
x_32 = x_96;
x_33 = x_91;
x_34 = x_80;
x_35 = x_81;
x_36 = x_82;
x_37 = x_83;
x_38 = x_84;
x_39 = lean_box(0);
goto block_78;
}
else
{
uint8_t x_121; 
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_96);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_96);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_97);
if (x_124 == 0)
{
return x_97;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_97, 0);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_95);
if (x_127 == 0)
{
return x_95;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_95, 0);
lean_inc(x_128);
lean_dec(x_95);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_90);
if (x_130 == 0)
{
return x_90;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_90, 0);
lean_inc(x_131);
lean_dec(x_90);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
case 5:
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_4);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_4, 0);
x_317 = lean_ctor_get(x_4, 1);
x_318 = lean_ctor_get(x_4, 2);
x_319 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_3, x_317, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_319, 0);
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_321, 0);
lean_ctor_set(x_4, 1, x_323);
lean_ctor_set(x_321, 0, x_4);
return x_319;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_321, 0);
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_321);
lean_ctor_set(x_4, 1, x_324);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_4);
lean_ctor_set(x_326, 1, x_325);
lean_ctor_set(x_319, 0, x_326);
return x_319;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_327 = lean_ctor_get(x_319, 0);
lean_inc(x_327);
lean_dec(x_319);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_328);
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_4);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
}
else
{
lean_free_object(x_4);
lean_dec(x_318);
lean_dec(x_316);
return x_319;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_4, 0);
x_334 = lean_ctor_get(x_4, 1);
x_335 = lean_ctor_get(x_4, 2);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_4);
x_336 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_3, x_334, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_341 = x_337;
} else {
 lean_dec_ref(x_337);
 x_341 = lean_box(0);
}
x_342 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_342, 0, x_333);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_335);
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_340);
if (lean_is_scalar(x_338)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_338;
}
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
else
{
lean_dec(x_335);
lean_dec(x_333);
return x_336;
}
}
}
default: 
{
uint8_t x_345; lean_object* x_346; 
lean_dec(x_2);
x_345 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
x_346 = l_Lean_Meta_Match_Pattern_toExpr(x_4, x_345, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_346) == 0)
{
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_347; 
lean_dec_ref(x_346);
lean_dec(x_8);
lean_dec_ref(x_1);
x_347 = !lean_is_exclusive(x_5);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_5, 0);
x_349 = l_Lean_Meta_getFVarLocalDecl___redArg(x_348, x_7, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_st_ref_take(x_6);
lean_inc_ref(x_4);
x_353 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_4);
x_354 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_3);
lean_ctor_set(x_354, 2, x_353);
x_355 = lean_array_push(x_352, x_354);
x_356 = lean_st_ref_set(x_6, x_355);
lean_dec(x_6);
x_357 = l_Lean_Expr_fvarId_x21(x_348);
lean_dec(x_348);
lean_ctor_set(x_5, 0, x_357);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_4);
lean_ctor_set(x_358, 1, x_5);
lean_ctor_set(x_349, 0, x_358);
return x_349;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_359 = lean_ctor_get(x_349, 0);
lean_inc(x_359);
lean_dec(x_349);
x_360 = lean_st_ref_take(x_6);
lean_inc_ref(x_4);
x_361 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_4);
x_362 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_3);
lean_ctor_set(x_362, 2, x_361);
x_363 = lean_array_push(x_360, x_362);
x_364 = lean_st_ref_set(x_6, x_363);
lean_dec(x_6);
x_365 = l_Lean_Expr_fvarId_x21(x_348);
lean_dec(x_348);
lean_ctor_set(x_5, 0, x_365);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_4);
lean_ctor_set(x_366, 1, x_5);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
}
else
{
uint8_t x_368; 
lean_free_object(x_5);
lean_dec(x_348);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_368 = !lean_is_exclusive(x_349);
if (x_368 == 0)
{
return x_349;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_349, 0);
lean_inc(x_369);
lean_dec(x_349);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_5, 0);
lean_inc(x_371);
lean_dec(x_5);
x_372 = l_Lean_Meta_getFVarLocalDecl___redArg(x_371, x_7, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_st_ref_take(x_6);
lean_inc_ref(x_4);
x_376 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_4);
x_377 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_3);
lean_ctor_set(x_377, 2, x_376);
x_378 = lean_array_push(x_375, x_377);
x_379 = lean_st_ref_set(x_6, x_378);
lean_dec(x_6);
x_380 = l_Lean_Expr_fvarId_x21(x_371);
lean_dec(x_371);
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_4);
lean_ctor_set(x_382, 1, x_381);
if (lean_is_scalar(x_374)) {
 x_383 = lean_alloc_ctor(0, 1, 0);
} else {
 x_383 = x_374;
}
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_371);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_384 = lean_ctor_get(x_372, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_385 = x_372;
} else {
 lean_dec_ref(x_372);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_384);
return x_386;
}
}
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_5);
x_387 = lean_ctor_get(x_346, 0);
lean_inc(x_387);
lean_dec_ref(x_346);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_3);
x_388 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType(x_1, x_3, x_387, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
x_390 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__7));
lean_inc(x_10);
lean_inc_ref(x_9);
x_391 = l_Lean_Core_mkFreshUserName(x_390, x_9, x_10);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
lean_dec_ref(x_391);
x_393 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__4___boxed), 9, 2);
lean_closure_set(x_393, 0, x_4);
lean_closure_set(x_393, 1, x_3);
x_394 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg(x_392, x_389, x_393, x_6, x_7, x_8, x_9, x_10);
return x_394;
}
else
{
uint8_t x_395; 
lean_dec(x_389);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_395 = !lean_is_exclusive(x_391);
if (x_395 == 0)
{
return x_391;
}
else
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_391, 0);
lean_inc(x_396);
lean_dec(x_391);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_398 = !lean_is_exclusive(x_388);
if (x_398 == 0)
{
return x_388;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_388, 0);
lean_inc(x_399);
lean_dec(x_388);
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_399);
return x_400;
}
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_401 = !lean_is_exclusive(x_346);
if (x_401 == 0)
{
return x_346;
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_346, 0);
lean_inc(x_402);
lean_dec(x_346);
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_402);
return x_403;
}
}
}
}
block_22:
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__5___redArg(x_12, x_13, x_20, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_14)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_14;
}
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget_borrowed(x_1, x_13);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
x_20 = lean_infer_type(x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__0));
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_shiftr(x_13, x_23);
x_25 = lean_array_get(x_22, x_2, x_24);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_30 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_29, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_76; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Expr_getForallBody(x_21);
lean_dec(x_21);
x_33 = l_Lean_Expr_getAppFn(x_32);
lean_dec_ref(x_32);
x_34 = l_Lean_Expr_constName_x21(x_33);
lean_dec_ref(x_33);
x_76 = lean_unbox(x_31);
lean_dec(x_31);
if (x_76 == 0)
{
lean_free_object(x_25);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_35 = x_12;
x_36 = x_13;
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4;
lean_inc(x_19);
x_78 = l_Lean_MessageData_ofExpr(x_19);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_78);
lean_ctor_set(x_25, 0, x_77);
x_79 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_25);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_28);
x_81 = l_Nat_reprFast(x_28);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Meta_Match_instInhabitedPattern_default;
x_88 = lean_array_get_borrowed(x_87, x_12, x_28);
lean_inc(x_88);
x_89 = l_Lean_Meta_Match_Pattern_toMessageData(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_29, x_90, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_35 = x_12;
x_36 = x_13;
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = lean_box(0);
goto block_75;
}
else
{
uint8_t x_92; 
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
block_75:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_Meta_Match_instInhabitedPattern_default;
x_44 = lean_array_get_borrowed(x_43, x_35, x_28);
lean_inc(x_19);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_19);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc(x_44);
lean_inc(x_4);
lean_inc_ref(x_3);
x_46 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_3, x_4, x_34, x_44, x_45, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_instInhabitedExpr;
x_51 = lean_nat_add(x_36, x_23);
x_52 = lean_array_get_borrowed(x_50, x_1, x_51);
lean_dec(x_51);
x_53 = l_Lean_Meta_getFVarLocalDecl___redArg(x_52, x_38, x_40, x_41);
lean_dec(x_41);
lean_dec_ref(x_40);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_st_ref_take(x_37);
lean_inc(x_48);
x_56 = lean_array_set(x_35, x_28, x_48);
lean_dec(x_28);
x_57 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_48);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_27);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_array_push(x_55, x_58);
x_60 = lean_st_ref_set(x_37, x_59);
lean_dec(x_37);
x_61 = lean_array_push(x_56, x_49);
x_62 = l_Lean_Expr_fvarId_x21(x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_array_push(x_61, x_63);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_add(x_36, x_65);
lean_dec(x_36);
if (lean_is_scalar(x_14)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_14;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_5 = x_67;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
return x_53;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_53, 0);
lean_inc(x_70);
lean_dec(x_53);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_72 = !lean_is_exclusive(x_46);
if (x_72 == 0)
{
return x_46;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
lean_dec(x_46);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_25);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_95 = !lean_is_exclusive(x_30);
if (x_95 == 0)
{
return x_30;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_30, 0);
lean_inc(x_96);
lean_dec(x_30);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_25, 0);
x_99 = lean_ctor_get(x_25, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_25);
x_100 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_101 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__2___redArg(x_100, x_9);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_147; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = l_Lean_Expr_getForallBody(x_21);
lean_dec(x_21);
x_104 = l_Lean_Expr_getAppFn(x_103);
lean_dec_ref(x_103);
x_105 = l_Lean_Expr_constName_x21(x_104);
lean_dec_ref(x_104);
x_147 = lean_unbox(x_102);
lean_dec(x_102);
if (x_147 == 0)
{
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_106 = x_12;
x_107 = x_13;
x_108 = x_6;
x_109 = x_7;
x_110 = x_8;
x_111 = x_9;
x_112 = x_10;
x_113 = lean_box(0);
goto block_146;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_148 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4;
lean_inc(x_19);
x_149 = l_Lean_MessageData_ofExpr(x_19);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
lean_inc(x_99);
x_153 = l_Nat_reprFast(x_99);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Lean_MessageData_ofFormat(x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_Meta_Match_instInhabitedPattern_default;
x_160 = lean_array_get_borrowed(x_159, x_12, x_99);
lean_inc(x_160);
x_161 = l_Lean_Meta_Match_Pattern_toMessageData(x_160);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_100, x_162, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_106 = x_12;
x_107 = x_13;
x_108 = x_6;
x_109 = x_7;
x_110 = x_8;
x_111 = x_9;
x_112 = x_10;
x_113 = lean_box(0);
goto block_146;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
block_146:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = l_Lean_Meta_Match_instInhabitedPattern_default;
x_115 = lean_array_get_borrowed(x_114, x_106, x_99);
lean_inc(x_19);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_19);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc(x_115);
lean_inc(x_4);
lean_inc_ref(x_3);
x_117 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_3, x_4, x_105, x_115, x_116, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_instInhabitedExpr;
x_122 = lean_nat_add(x_107, x_23);
x_123 = lean_array_get_borrowed(x_121, x_1, x_122);
lean_dec(x_122);
x_124 = l_Lean_Meta_getFVarLocalDecl___redArg(x_123, x_109, x_111, x_112);
lean_dec(x_112);
lean_dec_ref(x_111);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_st_ref_take(x_108);
lean_inc(x_119);
x_127 = lean_array_set(x_106, x_99, x_119);
lean_dec(x_99);
x_128 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern(x_119);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_98);
lean_ctor_set(x_129, 2, x_128);
x_130 = lean_array_push(x_126, x_129);
x_131 = lean_st_ref_set(x_108, x_130);
lean_dec(x_108);
x_132 = lean_array_push(x_127, x_120);
x_133 = l_Lean_Expr_fvarId_x21(x_123);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_array_push(x_132, x_134);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_nat_add(x_107, x_136);
lean_dec(x_107);
if (lean_is_scalar(x_14)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_14;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_5 = x_138;
goto _start;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_140 = lean_ctor_get(x_124, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_141 = x_124;
} else {
 lean_dec_ref(x_124);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_143 = lean_ctor_get(x_117, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_144 = x_117;
} else {
 lean_dec_ref(x_117);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_167 = lean_ctor_get(x_101, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_168 = x_101;
} else {
 lean_dec_ref(x_101);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_167);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_170 = !lean_is_exclusive(x_20);
if (x_170 == 0)
{
return x_20;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_20, 0);
lean_inc(x_171);
lean_dec(x_20);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_st_ref_get(x_11);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_3);
x_20 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4(x_9, x_2, x_3, x_4, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_Meta_Match_Pattern_toExpr(x_5, x_6, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_array_to_list(x_3);
x_30 = lean_array_to_list(x_23);
lean_inc(x_28);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_21, 1, x_31);
lean_ctor_set(x_21, 0, x_32);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_array_to_list(x_3);
x_36 = lean_array_to_list(x_23);
lean_inc(x_34);
x_37 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_21, 1, x_37);
lean_ctor_set(x_21, 0, x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_21);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_3);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = l_Lean_Meta_Match_Pattern_toExpr(x_5, x_6, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_array_to_list(x_3);
x_49 = lean_array_to_list(x_43);
lean_inc(x_47);
x_50 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_8);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_46;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_8);
lean_dec_ref(x_3);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_55 = x_44;
} else {
 lean_dec_ref(x_44);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_20, 0);
lean_inc(x_58);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_9);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___redArg(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_6);
x_18 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__10(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11_spec__15(x_1, x_2, x_13, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__9_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_14);
lean_dec(x_5);
x_8 = x_14;
goto block_13;
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_mk_empty_array_with_capacity(x_2);
x_18 = lean_st_mk_ref(x_17);
x_19 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_18);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_3, x_4, x_5, x_15, x_19, x_18, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_st_ref_get(x_18);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_array_size(x_22);
x_27 = 0;
lean_inc(x_22);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(x_26, x_27, x_22);
x_29 = lean_array_to_list(x_28);
lean_ctor_set(x_1, 0, x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_1);
x_31 = l_List_appendTR___redArg(x_6, x_30);
lean_inc(x_29);
x_32 = l_List_appendTR___redArg(x_7, x_29);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_21, 1, x_22);
lean_ctor_set(x_21, 0, x_33);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0___boxed), 6, 1);
lean_closure_set(x_34, 0, x_21);
x_35 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_29, x_34, x_9, x_10, x_11, x_12);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_array_size(x_22);
x_39 = 0;
lean_inc(x_22);
x_40 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(x_38, x_39, x_22);
x_41 = lean_array_to_list(x_40);
lean_ctor_set(x_1, 0, x_37);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_1);
x_43 = l_List_appendTR___redArg(x_6, x_42);
lean_inc(x_41);
x_44 = l_List_appendTR___redArg(x_7, x_41);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_22);
x_47 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0___boxed), 6, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_41, x_47, x_9, x_10, x_11, x_12);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_20, 0);
lean_inc(x_50);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_mk_empty_array_with_capacity(x_2);
x_55 = lean_st_mk_ref(x_54);
x_56 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_55);
x_57 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_3, x_4, x_5, x_52, x_56, x_55, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_st_ref_get(x_55);
lean_dec(x_55);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_array_size(x_59);
x_64 = 0;
lean_inc(x_59);
x_65 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__0(x_63, x_64, x_59);
x_66 = lean_array_to_list(x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_53);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_List_appendTR___redArg(x_6, x_68);
lean_inc(x_66);
x_70 = l_List_appendTR___redArg(x_7, x_66);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_8);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
if (lean_is_scalar(x_62)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_62;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_59);
x_73 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__0___boxed), 6, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_66, x_73, x_9, x_10, x_11, x_12);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_75 = lean_ctor_get(x_57, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_76 = x_57;
} else {
 lean_dec_ref(x_57);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_78 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1;
x_79 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0___redArg(x_78, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0;
lean_inc(x_4);
lean_inc(x_13);
x_16 = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), x_13, x_13, x_4, x_15);
x_17 = l_List_drop___redArg(x_4, x_13);
lean_dec(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___boxed), 13, 8);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_16);
lean_closure_set(x_18, 6, x_12);
lean_closure_set(x_18, 7, x_11);
x_19 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_12, x_18, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_apply_6(x_5, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget_borrowed(x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get_borrowed(x_17, x_4, x_15);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_18);
lean_inc(x_16);
lean_inc_ref(x_1);
x_19 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType(x_1, x_16, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0___boxed), 12, 6);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_2);
lean_closure_set(x_21, 5, x_5);
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelow_spec__4___closed__1));
x_23 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_go_spec__0___redArg(x_22, x_20, x_21, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = lean_nat_add(x_2, x_13);
x_16 = l_Array_insertIdx_x21___redArg(x_3, x_15, x_7);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_4, x_5, x_14, x_16, x_6, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_DeclNameGenerator_mkUniqueName(x_7, x_5, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 3);
lean_dec(x_13);
lean_ctor_set(x_11, 3, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 2);
x_19 = lean_ctor_get(x_11, 4);
x_20 = lean_ctor_get(x_11, 5);
x_21 = lean_ctor_get(x_11, 6);
x_22 = lean_ctor_get(x_11, 7);
x_23 = lean_ctor_get(x_11, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_23);
x_25 = lean_st_ref_set(x_2, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_9);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = 1;
x_11 = l_Lean_Meta_mkForallFVars(x_3, x_1, x_2, x_9, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__0___boxed), 8, 2);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_2, x_3, x_4, x_9, x_17, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set(x_21, 3, x_7);
lean_ctor_set(x_21, 4, x_8);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set(x_23, 3, x_7);
lean_ctor_set(x_23, 4, x_8);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = 1;
x_11 = l_Lean_Meta_mkLambdaFVars(x_3, x_1, x_2, x_9, x_2, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__2___boxed), 8, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_12);
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_exceptEmoji___redArg(x_3);
x_10 = l_Lean_stringToMessageData(x_9);
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_MatcherApp_toExpr(x_1);
x_14 = l_Lean_MessageData_ofExpr(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_to_list(x_2);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_18, x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_mkForallFVars(x_4, x_1, x_2, x_3, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(x_1);
x_18 = lean_box(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__5___boxed), 9, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_3, x_4, x_5, x_10, x_19, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_9);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_9);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_1);
x_18 = lean_unbox(x_2);
x_19 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_mkLambdaFVars(x_4, x_1, x_2, x_3, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_1);
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__7___boxed), 9, 3);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_mkForallFVars(x_4, x_1, x_2, x_3, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(x_1);
x_18 = lean_box(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__9___boxed), 9, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_3, x_4, x_5, x_10, x_19, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_9);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_9);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_1);
x_18 = lean_unbox(x_2);
x_19 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_mkLambdaFVars(x_4, x_1, x_2, x_3, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_1);
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__11___boxed), 9, 3);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addVars(x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; lean_object* x_13; 
x_7 = 1;
x_13 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
x_8 = x_1;
goto block_12;
}
else
{
lean_dec_ref(x_13);
x_8 = x_2;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(x_6, x_7, x_3, x_8, x_9);
lean_dec_ref(x_3);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_7, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget_borrowed(x_2, x_7);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_17 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(x_3, x_4, x_5, x_6, x_16, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_23 = x_8;
} else {
 lean_dec_ref(x_8);
 x_23 = lean_box(0);
}
x_24 = lean_array_push(x_22, x_19);
x_31 = lean_array_get_size(x_21);
x_32 = lean_nat_dec_lt(x_7, x_31);
if (x_32 == 0)
{
lean_dec(x_20);
x_25 = x_21;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_fget(x_21, x_7);
x_34 = lean_box(0);
x_35 = lean_array_fset(x_21, x_7, x_34);
x_36 = l_Array_append___redArg(x_33, x_20);
lean_dec(x_20);
x_37 = lean_array_fset(x_35, x_7, x_36);
x_25 = x_37;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_7, x_27);
lean_dec(x_7);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_17);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_17, x_28);
lean_dec(x_17);
x_30 = l_Lean_instInhabitedExpr;
x_31 = lean_array_get_borrowed(x_30, x_14, x_29);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_31);
x_32 = l_Lean_Meta_whnfCore(x_31, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Expr_getAppFn(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_1, 0);
x_37 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_36, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_42 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_40, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec_ref(x_42);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
x_46 = lean_ctor_get(x_20, 2);
x_47 = lean_ctor_get(x_20, 3);
x_48 = lean_ctor_get(x_20, 4);
x_49 = lean_array_mk(x_47);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_add(x_29, x_28);
x_52 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
lean_ctor_set(x_12, 1, x_52);
lean_ctor_set(x_12, 0, x_24);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_29);
lean_inc(x_40);
lean_inc(x_3);
lean_inc_ref(x_2);
x_53 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_50, x_49, x_2, x_3, x_40, x_29, x_25, x_12, x_5, x_6, x_7, x_8);
lean_dec_ref(x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = l_Lean_Expr_getAppNumArgs(x_33);
x_59 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_58);
x_60 = lean_mk_array(x_58, x_59);
x_61 = lean_nat_sub(x_58, x_28);
lean_dec(x_58);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_60, x_61);
x_63 = l_Lean_mkAppN(x_41, x_62);
lean_dec_ref(x_62);
x_64 = l_Array_insertIdx_x21___redArg(x_14, x_51, x_63);
x_65 = lean_box(0);
x_66 = l_Array_insertIdx_x21___redArg(x_46, x_51, x_65);
lean_dec(x_51);
x_67 = lean_array_to_list(x_57);
lean_ctor_set(x_20, 3, x_67);
lean_ctor_set(x_20, 2, x_66);
lean_inc(x_29);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_29);
x_68 = lean_array_push(x_23, x_38);
lean_ctor_set(x_54, 1, x_56);
lean_ctor_set(x_54, 0, x_68);
lean_ctor_set(x_11, 1, x_54);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_4, 0, x_64);
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = l_Lean_Expr_getAppNumArgs(x_33);
x_73 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_72);
x_74 = lean_mk_array(x_72, x_73);
x_75 = lean_nat_sub(x_72, x_28);
lean_dec(x_72);
x_76 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_74, x_75);
x_77 = l_Lean_mkAppN(x_41, x_76);
lean_dec_ref(x_76);
x_78 = l_Array_insertIdx_x21___redArg(x_14, x_51, x_77);
x_79 = lean_box(0);
x_80 = l_Array_insertIdx_x21___redArg(x_46, x_51, x_79);
lean_dec(x_51);
x_81 = lean_array_to_list(x_71);
lean_ctor_set(x_20, 3, x_81);
lean_ctor_set(x_20, 2, x_80);
lean_inc(x_29);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_29);
x_82 = lean_array_push(x_23, x_38);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_11, 1, x_83);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_4, 0, x_78);
goto _start;
}
}
else
{
uint8_t x_85; 
lean_dec(x_51);
lean_free_object(x_20);
lean_dec(x_48);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_free_object(x_38);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_85 = !lean_is_exclusive(x_53);
if (x_85 == 0)
{
return x_53;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_53, 0);
lean_inc(x_86);
lean_dec(x_53);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_20, 0);
x_89 = lean_ctor_get(x_20, 1);
x_90 = lean_ctor_get(x_20, 2);
x_91 = lean_ctor_get(x_20, 3);
x_92 = lean_ctor_get(x_20, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_20);
x_93 = lean_array_mk(x_91);
x_94 = lean_array_get_size(x_93);
x_95 = lean_nat_add(x_29, x_28);
x_96 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
lean_ctor_set(x_12, 1, x_96);
lean_ctor_set(x_12, 0, x_24);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_29);
lean_inc(x_40);
lean_inc(x_3);
lean_inc_ref(x_2);
x_97 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_94, x_93, x_2, x_3, x_40, x_29, x_25, x_12, x_5, x_6, x_7, x_8);
lean_dec_ref(x_93);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = l_Lean_Expr_getAppNumArgs(x_33);
x_103 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_102);
x_104 = lean_mk_array(x_102, x_103);
x_105 = lean_nat_sub(x_102, x_28);
lean_dec(x_102);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_104, x_105);
x_107 = l_Lean_mkAppN(x_41, x_106);
lean_dec_ref(x_106);
x_108 = l_Array_insertIdx_x21___redArg(x_14, x_95, x_107);
x_109 = lean_box(0);
x_110 = l_Array_insertIdx_x21___redArg(x_90, x_95, x_109);
lean_dec(x_95);
x_111 = lean_array_to_list(x_100);
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_88);
lean_ctor_set(x_112, 1, x_89);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
lean_ctor_set(x_112, 4, x_92);
lean_inc(x_29);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_29);
x_113 = lean_array_push(x_23, x_38);
if (lean_is_scalar(x_101)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_101;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_11, 1, x_114);
lean_ctor_set(x_11, 0, x_112);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_4, 0, x_108);
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_116 = lean_ctor_get(x_97, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_117 = x_97;
} else {
 lean_dec_ref(x_97);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_38);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_20);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_119 = !lean_is_exclusive(x_42);
if (x_119 == 0)
{
return x_42;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_42, 0);
lean_inc(x_120);
lean_dec(x_42);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_38, 0);
x_123 = lean_ctor_get(x_38, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_38);
lean_inc(x_122);
x_124 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_122, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_124);
x_125 = lean_ctor_get(x_20, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_20, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_20, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 x_130 = x_20;
} else {
 lean_dec_ref(x_20);
 x_130 = lean_box(0);
}
x_131 = lean_array_mk(x_128);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_add(x_29, x_28);
x_134 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
lean_ctor_set(x_12, 1, x_134);
lean_ctor_set(x_12, 0, x_24);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_29);
lean_inc(x_122);
lean_inc(x_3);
lean_inc_ref(x_2);
x_135 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_132, x_131, x_2, x_3, x_122, x_29, x_25, x_12, x_5, x_6, x_7, x_8);
lean_dec_ref(x_131);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = l_Lean_Expr_getAppNumArgs(x_33);
x_141 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_nat_sub(x_140, x_28);
lean_dec(x_140);
x_144 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_142, x_143);
x_145 = l_Lean_mkAppN(x_123, x_144);
lean_dec_ref(x_144);
x_146 = l_Array_insertIdx_x21___redArg(x_14, x_133, x_145);
x_147 = lean_box(0);
x_148 = l_Array_insertIdx_x21___redArg(x_127, x_133, x_147);
lean_dec(x_133);
x_149 = lean_array_to_list(x_138);
if (lean_is_scalar(x_130)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_130;
}
lean_ctor_set(x_150, 0, x_125);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_150, 2, x_148);
lean_ctor_set(x_150, 3, x_149);
lean_ctor_set(x_150, 4, x_129);
lean_inc(x_29);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_29);
lean_ctor_set(x_151, 1, x_122);
x_152 = lean_array_push(x_23, x_151);
if (lean_is_scalar(x_139)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_139;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_137);
lean_ctor_set(x_11, 1, x_153);
lean_ctor_set(x_11, 0, x_150);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_4, 0, x_146);
goto _start;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_ctor_get(x_135, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_156 = x_135;
} else {
 lean_dec_ref(x_135);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_33);
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_20);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_158 = lean_ctor_get(x_124, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_159 = x_124;
} else {
 lean_dec_ref(x_124);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_33);
lean_ctor_set(x_10, 0, x_29);
goto _start;
}
}
else
{
lean_dec_ref(x_34);
lean_dec(x_33);
lean_ctor_set(x_10, 0, x_29);
goto _start;
}
}
else
{
uint8_t x_163; 
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_20);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_163 = !lean_is_exclusive(x_32);
if (x_163 == 0)
{
return x_32;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_32, 0);
lean_inc(x_164);
lean_dec(x_32);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_12, 0);
x_167 = lean_ctor_get(x_12, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_12);
x_168 = lean_unsigned_to_nat(0u);
x_169 = lean_nat_dec_lt(x_168, x_17);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_11, 1, x_170);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_sub(x_17, x_172);
lean_dec(x_17);
x_174 = l_Lean_instInhabitedExpr;
x_175 = lean_array_get_borrowed(x_174, x_14, x_173);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_175);
x_176 = l_Lean_Meta_whnfCore(x_175, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = l_Lean_Expr_getAppFn(x_177);
if (lean_obj_tag(x_178) == 1)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = lean_ctor_get(x_1, 0);
x_181 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_180, x_179);
lean_dec(x_179);
if (lean_obj_tag(x_181) == 1)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
lean_inc(x_183);
x_186 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_183, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_186);
x_187 = lean_ctor_get(x_20, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_20, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_20, 4);
lean_inc(x_191);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 x_192 = x_20;
} else {
 lean_dec_ref(x_20);
 x_192 = lean_box(0);
}
x_193 = lean_array_mk(x_190);
x_194 = lean_array_get_size(x_193);
x_195 = lean_nat_add(x_173, x_172);
x_196 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_167);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_173);
lean_inc(x_183);
lean_inc(x_3);
lean_inc_ref(x_2);
x_198 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_194, x_193, x_2, x_3, x_183, x_173, x_168, x_197, x_5, x_6, x_7, x_8);
lean_dec_ref(x_193);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
x_203 = l_Lean_Expr_getAppNumArgs(x_177);
x_204 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_203);
x_205 = lean_mk_array(x_203, x_204);
x_206 = lean_nat_sub(x_203, x_172);
lean_dec(x_203);
x_207 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_177, x_205, x_206);
x_208 = l_Lean_mkAppN(x_184, x_207);
lean_dec_ref(x_207);
x_209 = l_Array_insertIdx_x21___redArg(x_14, x_195, x_208);
x_210 = lean_box(0);
x_211 = l_Array_insertIdx_x21___redArg(x_189, x_195, x_210);
lean_dec(x_195);
x_212 = lean_array_to_list(x_201);
if (lean_is_scalar(x_192)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_192;
}
lean_ctor_set(x_213, 0, x_187);
lean_ctor_set(x_213, 1, x_188);
lean_ctor_set(x_213, 2, x_211);
lean_ctor_set(x_213, 3, x_212);
lean_ctor_set(x_213, 4, x_191);
lean_inc(x_173);
if (lean_is_scalar(x_185)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_185;
}
lean_ctor_set(x_214, 0, x_173);
lean_ctor_set(x_214, 1, x_183);
x_215 = lean_array_push(x_166, x_214);
if (lean_is_scalar(x_202)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_202;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_200);
lean_ctor_set(x_11, 1, x_216);
lean_ctor_set(x_11, 0, x_213);
lean_ctor_set(x_10, 0, x_173);
lean_ctor_set(x_4, 0, x_209);
goto _start;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_195);
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_177);
lean_dec(x_173);
lean_dec(x_166);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_218 = lean_ctor_get(x_198, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_219 = x_198;
} else {
 lean_dec_ref(x_198);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_177);
lean_dec(x_173);
lean_dec(x_167);
lean_dec(x_166);
lean_free_object(x_11);
lean_dec(x_20);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_221 = lean_ctor_get(x_186, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_222 = x_186;
} else {
 lean_dec_ref(x_186);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_221);
return x_223;
}
}
else
{
lean_object* x_224; 
lean_dec(x_181);
lean_dec(x_177);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_166);
lean_ctor_set(x_224, 1, x_167);
lean_ctor_set(x_11, 1, x_224);
lean_ctor_set(x_10, 0, x_173);
goto _start;
}
}
else
{
lean_object* x_226; 
lean_dec_ref(x_178);
lean_dec(x_177);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_166);
lean_ctor_set(x_226, 1, x_167);
lean_ctor_set(x_11, 1, x_226);
lean_ctor_set(x_10, 0, x_173);
goto _start;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_173);
lean_dec(x_167);
lean_dec(x_166);
lean_free_object(x_11);
lean_dec(x_20);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_176, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_229 = x_176;
} else {
 lean_dec_ref(x_176);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_11, 0);
lean_inc(x_231);
lean_dec(x_11);
x_232 = lean_ctor_get(x_12, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_12, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_234 = x_12;
} else {
 lean_dec_ref(x_12);
 x_234 = lean_box(0);
}
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_nat_dec_lt(x_235, x_17);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_232);
lean_ctor_set(x_237, 1, x_233);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_10, 1, x_238);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_4);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_nat_sub(x_17, x_240);
lean_dec(x_17);
x_242 = l_Lean_instInhabitedExpr;
x_243 = lean_array_get_borrowed(x_242, x_14, x_241);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_243);
x_244 = l_Lean_Meta_whnfCore(x_243, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_246 = l_Lean_Expr_getAppFn(x_245);
if (lean_obj_tag(x_246) == 1)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = lean_ctor_get(x_1, 0);
x_249 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_248, x_247);
lean_dec(x_247);
if (lean_obj_tag(x_249) == 1)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
lean_inc(x_251);
x_254 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_251, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec_ref(x_254);
x_255 = lean_ctor_get(x_231, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_231, 1);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_231, 2);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_231, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_231, 4);
lean_inc(x_259);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 lean_ctor_release(x_231, 3);
 lean_ctor_release(x_231, 4);
 x_260 = x_231;
} else {
 lean_dec_ref(x_231);
 x_260 = lean_box(0);
}
x_261 = lean_array_mk(x_258);
x_262 = lean_array_get_size(x_261);
x_263 = lean_nat_add(x_241, x_240);
x_264 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
if (lean_is_scalar(x_234)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_234;
}
lean_ctor_set(x_265, 0, x_233);
lean_ctor_set(x_265, 1, x_264);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_241);
lean_inc(x_251);
lean_inc(x_3);
lean_inc_ref(x_2);
x_266 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_262, x_261, x_2, x_3, x_251, x_241, x_235, x_265, x_5, x_6, x_7, x_8);
lean_dec_ref(x_261);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = l_Lean_Expr_getAppNumArgs(x_245);
x_272 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_271);
x_273 = lean_mk_array(x_271, x_272);
x_274 = lean_nat_sub(x_271, x_240);
lean_dec(x_271);
x_275 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_245, x_273, x_274);
x_276 = l_Lean_mkAppN(x_252, x_275);
lean_dec_ref(x_275);
x_277 = l_Array_insertIdx_x21___redArg(x_14, x_263, x_276);
x_278 = lean_box(0);
x_279 = l_Array_insertIdx_x21___redArg(x_257, x_263, x_278);
lean_dec(x_263);
x_280 = lean_array_to_list(x_269);
if (lean_is_scalar(x_260)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_260;
}
lean_ctor_set(x_281, 0, x_255);
lean_ctor_set(x_281, 1, x_256);
lean_ctor_set(x_281, 2, x_279);
lean_ctor_set(x_281, 3, x_280);
lean_ctor_set(x_281, 4, x_259);
lean_inc(x_241);
if (lean_is_scalar(x_253)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_253;
}
lean_ctor_set(x_282, 0, x_241);
lean_ctor_set(x_282, 1, x_251);
x_283 = lean_array_push(x_232, x_282);
if (lean_is_scalar(x_270)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_270;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_268);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set(x_10, 1, x_285);
lean_ctor_set(x_10, 0, x_241);
lean_ctor_set(x_4, 0, x_277);
goto _start;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_259);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_245);
lean_dec(x_241);
lean_dec(x_232);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_287 = lean_ctor_get(x_266, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_288 = x_266;
} else {
 lean_dec_ref(x_266);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_245);
lean_dec(x_241);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_290 = lean_ctor_get(x_254, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_291 = x_254;
} else {
 lean_dec_ref(x_254);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_249);
lean_dec(x_245);
if (lean_is_scalar(x_234)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_234;
}
lean_ctor_set(x_293, 0, x_232);
lean_ctor_set(x_293, 1, x_233);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_231);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_10, 1, x_294);
lean_ctor_set(x_10, 0, x_241);
goto _start;
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_246);
lean_dec(x_245);
if (lean_is_scalar(x_234)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_234;
}
lean_ctor_set(x_296, 0, x_232);
lean_ctor_set(x_296, 1, x_233);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_231);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set(x_10, 1, x_297);
lean_ctor_set(x_10, 0, x_241);
goto _start;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_241);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_free_object(x_10);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_299 = lean_ctor_get(x_244, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_300 = x_244;
} else {
 lean_dec_ref(x_244);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_302 = lean_ctor_get(x_10, 0);
lean_inc(x_302);
lean_dec(x_10);
x_303 = lean_ctor_get(x_11, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_304 = x_11;
} else {
 lean_dec_ref(x_11);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_12, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_12, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_307 = x_12;
} else {
 lean_dec_ref(x_12);
 x_307 = lean_box(0);
}
x_308 = lean_unsigned_to_nat(0u);
x_309 = lean_nat_dec_lt(x_308, x_302);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_307)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_307;
}
lean_ctor_set(x_310, 0, x_305);
lean_ctor_set(x_310, 1, x_306);
if (lean_is_scalar(x_304)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_304;
}
lean_ctor_set(x_311, 0, x_303);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_302);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_4, 1, x_312);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_4);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_314 = lean_unsigned_to_nat(1u);
x_315 = lean_nat_sub(x_302, x_314);
lean_dec(x_302);
x_316 = l_Lean_instInhabitedExpr;
x_317 = lean_array_get_borrowed(x_316, x_14, x_315);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_317);
x_318 = l_Lean_Meta_whnfCore(x_317, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec_ref(x_318);
x_320 = l_Lean_Expr_getAppFn(x_319);
if (lean_obj_tag(x_320) == 1)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = lean_ctor_get(x_1, 0);
x_323 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_322, x_321);
lean_dec(x_321);
if (lean_obj_tag(x_323) == 1)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec_ref(x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
lean_inc(x_325);
x_328 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_325, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec_ref(x_328);
x_329 = lean_ctor_get(x_303, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_303, 1);
lean_inc_ref(x_330);
x_331 = lean_ctor_get(x_303, 2);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_303, 3);
lean_inc(x_332);
x_333 = lean_ctor_get(x_303, 4);
lean_inc(x_333);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 lean_ctor_release(x_303, 3);
 lean_ctor_release(x_303, 4);
 x_334 = x_303;
} else {
 lean_dec_ref(x_303);
 x_334 = lean_box(0);
}
x_335 = lean_array_mk(x_332);
x_336 = lean_array_get_size(x_335);
x_337 = lean_nat_add(x_315, x_314);
x_338 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
if (lean_is_scalar(x_307)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_307;
}
lean_ctor_set(x_339, 0, x_306);
lean_ctor_set(x_339, 1, x_338);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_315);
lean_inc(x_325);
lean_inc(x_3);
lean_inc_ref(x_2);
x_340 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_336, x_335, x_2, x_3, x_325, x_315, x_308, x_339, x_5, x_6, x_7, x_8);
lean_dec_ref(x_335);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = l_Lean_Expr_getAppNumArgs(x_319);
x_346 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_345);
x_347 = lean_mk_array(x_345, x_346);
x_348 = lean_nat_sub(x_345, x_314);
lean_dec(x_345);
x_349 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_319, x_347, x_348);
x_350 = l_Lean_mkAppN(x_326, x_349);
lean_dec_ref(x_349);
x_351 = l_Array_insertIdx_x21___redArg(x_14, x_337, x_350);
x_352 = lean_box(0);
x_353 = l_Array_insertIdx_x21___redArg(x_331, x_337, x_352);
lean_dec(x_337);
x_354 = lean_array_to_list(x_343);
if (lean_is_scalar(x_334)) {
 x_355 = lean_alloc_ctor(0, 5, 0);
} else {
 x_355 = x_334;
}
lean_ctor_set(x_355, 0, x_329);
lean_ctor_set(x_355, 1, x_330);
lean_ctor_set(x_355, 2, x_353);
lean_ctor_set(x_355, 3, x_354);
lean_ctor_set(x_355, 4, x_333);
lean_inc(x_315);
if (lean_is_scalar(x_327)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_327;
}
lean_ctor_set(x_356, 0, x_315);
lean_ctor_set(x_356, 1, x_325);
x_357 = lean_array_push(x_305, x_356);
if (lean_is_scalar(x_344)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_344;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_342);
if (lean_is_scalar(x_304)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_304;
}
lean_ctor_set(x_359, 0, x_355);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_315);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_4, 1, x_360);
lean_ctor_set(x_4, 0, x_351);
goto _start;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_337);
lean_dec(x_334);
lean_dec(x_333);
lean_dec_ref(x_331);
lean_dec_ref(x_330);
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_319);
lean_dec(x_315);
lean_dec(x_305);
lean_dec(x_304);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_362 = lean_ctor_get(x_340, 0);
lean_inc(x_362);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_363 = x_340;
} else {
 lean_dec_ref(x_340);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_319);
lean_dec(x_315);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_365 = lean_ctor_get(x_328, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_366 = x_328;
} else {
 lean_dec_ref(x_328);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_323);
lean_dec(x_319);
if (lean_is_scalar(x_307)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_307;
}
lean_ctor_set(x_368, 0, x_305);
lean_ctor_set(x_368, 1, x_306);
if (lean_is_scalar(x_304)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_304;
}
lean_ctor_set(x_369, 0, x_303);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_315);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_4, 1, x_370);
goto _start;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec_ref(x_320);
lean_dec(x_319);
if (lean_is_scalar(x_307)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_307;
}
lean_ctor_set(x_372, 0, x_305);
lean_ctor_set(x_372, 1, x_306);
if (lean_is_scalar(x_304)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_304;
}
lean_ctor_set(x_373, 0, x_303);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set(x_4, 1, x_374);
goto _start;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_315);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_376 = lean_ctor_get(x_318, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_377 = x_318;
} else {
 lean_dec_ref(x_318);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_379 = lean_ctor_get(x_4, 0);
lean_inc(x_379);
lean_dec(x_4);
x_380 = lean_ctor_get(x_10, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_381 = x_10;
} else {
 lean_dec_ref(x_10);
 x_381 = lean_box(0);
}
x_382 = lean_ctor_get(x_11, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_383 = x_11;
} else {
 lean_dec_ref(x_11);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_12, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_12, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_386 = x_12;
} else {
 lean_dec_ref(x_12);
 x_386 = lean_box(0);
}
x_387 = lean_unsigned_to_nat(0u);
x_388 = lean_nat_dec_lt(x_387, x_380);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_386)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_386;
}
lean_ctor_set(x_389, 0, x_384);
lean_ctor_set(x_389, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_383;
}
lean_ctor_set(x_390, 0, x_382);
lean_ctor_set(x_390, 1, x_389);
if (lean_is_scalar(x_381)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_381;
}
lean_ctor_set(x_391, 0, x_380);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_379);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_393, 0, x_392);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = lean_unsigned_to_nat(1u);
x_395 = lean_nat_sub(x_380, x_394);
lean_dec(x_380);
x_396 = l_Lean_instInhabitedExpr;
x_397 = lean_array_get_borrowed(x_396, x_379, x_395);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_397);
x_398 = l_Lean_Meta_whnfCore(x_397, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = l_Lean_Expr_getAppFn(x_399);
if (lean_obj_tag(x_400) == 1)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_402 = lean_ctor_get(x_1, 0);
x_403 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_isIH_spec__0___redArg(x_402, x_401);
lean_dec(x_401);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec_ref(x_403);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
lean_inc(x_405);
x_408 = l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0(x_405, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec_ref(x_408);
x_409 = lean_ctor_get(x_382, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_382, 1);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_382, 2);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_382, 3);
lean_inc(x_412);
x_413 = lean_ctor_get(x_382, 4);
lean_inc(x_413);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 lean_ctor_release(x_382, 4);
 x_414 = x_382;
} else {
 lean_dec_ref(x_382);
 x_414 = lean_box(0);
}
x_415 = lean_array_mk(x_412);
x_416 = lean_array_get_size(x_415);
x_417 = lean_nat_add(x_395, x_394);
x_418 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0;
if (lean_is_scalar(x_386)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_386;
}
lean_ctor_set(x_419, 0, x_385);
lean_ctor_set(x_419, 1, x_418);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_395);
lean_inc(x_405);
lean_inc(x_3);
lean_inc_ref(x_2);
x_420 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_416, x_415, x_2, x_3, x_405, x_395, x_387, x_419, x_5, x_6, x_7, x_8);
lean_dec_ref(x_415);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_424 = x_421;
} else {
 lean_dec_ref(x_421);
 x_424 = lean_box(0);
}
x_425 = l_Lean_Expr_getAppNumArgs(x_399);
x_426 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0;
lean_inc(x_425);
x_427 = lean_mk_array(x_425, x_426);
x_428 = lean_nat_sub(x_425, x_394);
lean_dec(x_425);
x_429 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_399, x_427, x_428);
x_430 = l_Lean_mkAppN(x_406, x_429);
lean_dec_ref(x_429);
x_431 = l_Array_insertIdx_x21___redArg(x_379, x_417, x_430);
x_432 = lean_box(0);
x_433 = l_Array_insertIdx_x21___redArg(x_411, x_417, x_432);
lean_dec(x_417);
x_434 = lean_array_to_list(x_423);
if (lean_is_scalar(x_414)) {
 x_435 = lean_alloc_ctor(0, 5, 0);
} else {
 x_435 = x_414;
}
lean_ctor_set(x_435, 0, x_409);
lean_ctor_set(x_435, 1, x_410);
lean_ctor_set(x_435, 2, x_433);
lean_ctor_set(x_435, 3, x_434);
lean_ctor_set(x_435, 4, x_413);
lean_inc(x_395);
if (lean_is_scalar(x_407)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_407;
}
lean_ctor_set(x_436, 0, x_395);
lean_ctor_set(x_436, 1, x_405);
x_437 = lean_array_push(x_384, x_436);
if (lean_is_scalar(x_424)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_424;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_422);
if (lean_is_scalar(x_383)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_383;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_438);
if (lean_is_scalar(x_381)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_381;
}
lean_ctor_set(x_440, 0, x_395);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_431);
lean_ctor_set(x_441, 1, x_440);
x_4 = x_441;
goto _start;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_409);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_399);
lean_dec(x_395);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_443 = lean_ctor_get(x_420, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_444 = x_420;
} else {
 lean_dec_ref(x_420);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_399);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_446 = lean_ctor_get(x_408, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_447 = x_408;
} else {
 lean_dec_ref(x_408);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_446);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_403);
lean_dec(x_399);
if (lean_is_scalar(x_386)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_386;
}
lean_ctor_set(x_449, 0, x_384);
lean_ctor_set(x_449, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_383;
}
lean_ctor_set(x_450, 0, x_382);
lean_ctor_set(x_450, 1, x_449);
if (lean_is_scalar(x_381)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_381;
}
lean_ctor_set(x_451, 0, x_395);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_379);
lean_ctor_set(x_452, 1, x_451);
x_4 = x_452;
goto _start;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec_ref(x_400);
lean_dec(x_399);
if (lean_is_scalar(x_386)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_386;
}
lean_ctor_set(x_454, 0, x_384);
lean_ctor_set(x_454, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_383;
}
lean_ctor_set(x_455, 0, x_382);
lean_ctor_set(x_455, 1, x_454);
if (lean_is_scalar(x_381)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_381;
}
lean_ctor_set(x_456, 0, x_395);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_379);
lean_ctor_set(x_457, 1, x_456);
x_4 = x_457;
goto _start;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_459 = lean_ctor_get(x_398, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_460 = x_398;
} else {
 lean_dec_ref(x_398);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
if (x_1 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_dec_ref(x_7);
return x_6;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_List_lengthTR___redArg(x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0_spec__0_spec__5(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
x_13 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_12, x_14, x_11);
lean_ctor_set(x_6, 1, x_15);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
x_22 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_21, x_23, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg(x_1, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
x_13 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_12, x_14, x_11);
lean_ctor_set(x_6, 0, x_15);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
x_22 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_21, x_23, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg(x_1, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_18);
x_22 = lean_array_size(x_21);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg(x_19, x_20, x_21, x_22, x_23, x_4);
lean_dec_ref(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_10 = x_25;
x_11 = lean_box(0);
goto block_15;
}
else
{
return x_24;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_18);
x_29 = lean_array_size(x_28);
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg(x_26, x_27, x_28, x_29, x_30, x_4);
lean_dec_ref(x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_10 = x_32;
x_11 = lean_box(0);
goto block_15;
}
else
{
return x_31;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvar___override(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_4);
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1;
x_15 = l_Lean_LocalDecl_toExpr(x_11);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_ofName(x_12);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_array_size(x_13);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0(x_23, x_24, x_13);
x_26 = lean_array_to_list(x_25);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_26, x_27);
x_29 = l_Lean_MessageData_ofList(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
x_7 = x_30;
goto block_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_33);
lean_dec_ref(x_4);
x_34 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6;
x_35 = l_Lean_LocalDecl_toExpr(x_31);
x_36 = l_Lean_MessageData_ofExpr(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Nat_reprFast(x_32);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_MessageData_ofFormat(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_array_size(x_33);
x_46 = 0;
x_47 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__0(x_45, x_46, x_33);
x_48 = lean_array_to_list(x_47);
x_49 = lean_box(0);
x_50 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_48, x_49);
x_51 = l_Lean_MessageData_ofList(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
x_7 = x_52;
goto block_10;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_LocalDecl_toExpr(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13;
x_2 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_inc(x_1);
x_172 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_16);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
x_155 = x_14;
x_156 = x_15;
x_157 = x_16;
x_158 = x_17;
x_159 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17;
lean_inc_ref(x_2);
x_176 = lean_array_to_list(x_2);
x_177 = lean_box(0);
x_178 = l_List_mapTR_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__11(x_176, x_177);
x_179 = l_Lean_MessageData_ofList(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_1);
x_181 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_180, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_181) == 0)
{
lean_dec_ref(x_181);
x_155 = x_14;
x_156 = x_15;
x_157 = x_16;
x_158 = x_17;
x_159 = lean_box(0);
goto block_171;
}
else
{
uint8_t x_182; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
return x_181;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
block_108:
{
size_t x_27; lean_object* x_28; 
x_27 = lean_array_size(x_2);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9(x_2, x_27, x_20, x_3, x_22, x_23, x_24, x_25);
lean_dec_ref(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_30 = lean_apply_7(x_4, x_29, x_21, x_22, x_23, x_24, x_25, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = 1;
x_33 = l_Lean_Meta_mkLambdaFVars(x_19, x_31, x_5, x_6, x_5, x_6, x_32, x_22, x_23, x_24, x_25);
lean_dec_ref(x_19);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_1);
x_36 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_24);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_free_object(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_36);
x_40 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_41 = l_Nat_reprFast(x_7);
lean_ctor_set_tag(x_33, 3);
lean_ctor_set(x_33, 0, x_41);
x_42 = l_Lean_MessageData_ofFormat(x_33);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_MessageData_ofExpr(x_8);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_35);
x_50 = l_Lean_MessageData_ofExpr(x_35);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_51, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_35);
return x_52;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_35);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_free_object(x_33);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_35);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_63 = l_Nat_reprFast(x_7);
lean_ctor_set_tag(x_33, 3);
lean_ctor_set(x_33, 0, x_63);
x_64 = l_Lean_MessageData_ofFormat(x_33);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MessageData_ofExpr(x_8);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_35);
x_72 = l_Lean_MessageData_ofExpr(x_35);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_73, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_75 = x_74;
} else {
 lean_dec_ref(x_74);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_35);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_35);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_33, 0);
lean_inc(x_80);
lean_dec(x_33);
lean_inc(x_1);
x_81 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_24);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_unbox(x_82);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_80);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
x_86 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_87 = l_Nat_reprFast(x_7);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_MessageData_ofFormat(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_MessageData_ofExpr(x_8);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_80);
x_97 = l_Lean_MessageData_ofExpr(x_80);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_98, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_100 = x_99;
} else {
 lean_dec_ref(x_99);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_80);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_80);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_33;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_30;
}
}
else
{
uint8_t x_105; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_28);
if (x_105 == 0)
{
return x_28;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_28, 0);
lean_inc(x_106);
lean_dec(x_28);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
block_154:
{
lean_object* x_117; uint8_t x_118; 
lean_inc(x_1);
x_117 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_113);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_free_object(x_117);
lean_dec(x_9);
x_19 = x_110;
x_20 = x_109;
x_21 = x_116;
x_22 = x_115;
x_23 = x_114;
x_24 = x_113;
x_25 = x_111;
x_26 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7;
x_122 = l_Nat_reprFast(x_9);
lean_ctor_set_tag(x_117, 3);
lean_ctor_set(x_117, 0, x_122);
x_123 = l_Lean_MessageData_ofFormat(x_117);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_inc_ref(x_110);
x_127 = lean_array_to_list(x_110);
x_128 = lean_box(0);
x_129 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_127, x_128);
x_130 = l_Lean_MessageData_ofList(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_1);
x_132 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_131, x_115, x_114, x_113, x_111);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_19 = x_110;
x_20 = x_109;
x_21 = x_116;
x_22 = x_115;
x_23 = x_114;
x_24 = x_113;
x_25 = x_111;
x_26 = lean_box(0);
goto block_108;
}
else
{
uint8_t x_133; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
return x_132;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_dec(x_9);
x_19 = x_110;
x_20 = x_109;
x_21 = x_116;
x_22 = x_115;
x_23 = x_114;
x_24 = x_113;
x_25 = x_111;
x_26 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_138 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7;
x_139 = l_Nat_reprFast(x_9);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lean_MessageData_ofFormat(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_inc_ref(x_110);
x_145 = lean_array_to_list(x_110);
x_146 = lean_box(0);
x_147 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_145, x_146);
x_148 = l_Lean_MessageData_ofList(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_1);
x_150 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_149, x_115, x_114, x_113, x_111);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_19 = x_110;
x_20 = x_109;
x_21 = x_116;
x_22 = x_115;
x_23 = x_114;
x_24 = x_113;
x_25 = x_111;
x_26 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
}
}
block_171:
{
lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_array_mk(x_10);
x_161 = lean_array_size(x_160);
x_162 = 0;
x_163 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8(x_161, x_162, x_160);
lean_inc(x_9);
x_164 = l_Array_extract___redArg(x_163, x_11, x_9);
lean_inc_ref(x_8);
x_165 = l_Lean_Expr_beta(x_8, x_164);
if (x_12 == 0)
{
x_109 = x_162;
x_110 = x_163;
x_111 = x_158;
x_112 = lean_box(0);
x_113 = x_157;
x_114 = x_156;
x_115 = x_155;
x_116 = x_165;
goto block_154;
}
else
{
if (x_13 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_array_get_size(x_163);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15;
x_170 = l_Lean_Expr_betaRev(x_165, x_169, x_5, x_5);
x_109 = x_162;
x_110 = x_163;
x_111 = x_158;
x_112 = lean_box(0);
x_113 = x_157;
x_114 = x_156;
x_115 = x_155;
x_116 = x_170;
goto block_154;
}
else
{
x_109 = x_162;
x_110 = x_163;
x_111 = x_158;
x_112 = lean_box(0);
x_113 = x_157;
x_114 = x_156;
x_115 = x_155;
x_116 = x_165;
goto block_154;
}
}
else
{
x_109 = x_162;
x_110 = x_163;
x_111 = x_158;
x_112 = lean_box(0);
x_113 = x_157;
x_114 = x_156;
x_115 = x_155;
x_116 = x_165;
goto block_154;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = lean_unbox(x_12);
x_22 = lean_unbox(x_13);
x_23 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_21, x_22, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 1)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = l_Lean_Meta_Match_instInhabitedAltLHS_default;
x_21 = lean_array_fget_borrowed(x_8, x_10);
lean_inc(x_10);
x_22 = l_List_get_x21Internal___redArg(x_20, x_1, x_10);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0;
x_25 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_26 = lean_array_get_borrowed(x_17, x_2, x_10);
x_27 = lean_array_get_borrowed(x_24, x_3, x_10);
x_28 = lean_nat_dec_eq(x_26, x_17);
x_29 = lean_box(x_18);
x_30 = lean_box(x_6);
x_31 = lean_box(x_28);
x_32 = lean_box(x_7);
lean_inc(x_23);
lean_inc(x_26);
lean_inc(x_21);
lean_inc(x_10);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_27);
x_33 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___boxed), 18, 13);
lean_closure_set(x_33, 0, x_25);
lean_closure_set(x_33, 1, x_27);
lean_closure_set(x_33, 2, x_4);
lean_closure_set(x_33, 3, x_5);
lean_closure_set(x_33, 4, x_29);
lean_closure_set(x_33, 5, x_30);
lean_closure_set(x_33, 6, x_10);
lean_closure_set(x_33, 7, x_21);
lean_closure_set(x_33, 8, x_26);
lean_closure_set(x_33, 9, x_23);
lean_closure_set(x_33, 10, x_17);
lean_closure_set(x_33, 11, x_31);
lean_closure_set(x_33, 12, x_32);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_34 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_23, x_33, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_9, x_36);
lean_dec(x_9);
x_38 = lean_nat_add(x_10, x_36);
lean_dec(x_10);
x_39 = lean_array_push(x_11, x_35);
x_9 = x_37;
x_10 = x_38;
x_11 = x_39;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_inc(x_1);
x_172 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_15);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17;
lean_inc_ref(x_2);
x_176 = lean_array_to_list(x_2);
x_177 = lean_box(0);
x_178 = l_List_mapTR_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__11(x_176, x_177);
x_179 = l_Lean_MessageData_ofList(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_1);
x_181 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_180, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_181) == 0)
{
lean_dec_ref(x_181);
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = lean_box(0);
goto block_171;
}
else
{
uint8_t x_182; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
return x_181;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
block_108:
{
size_t x_26; lean_object* x_27; 
x_26 = lean_array_size(x_2);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__9(x_2, x_26, x_20, x_3, x_21, x_22, x_23, x_24);
lean_dec_ref(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_29 = lean_apply_7(x_4, x_28, x_18, x_21, x_22, x_23, x_24, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = 1;
x_32 = 1;
x_33 = l_Lean_Meta_mkLambdaFVars(x_19, x_30, x_5, x_31, x_5, x_31, x_32, x_21, x_22, x_23, x_24);
lean_dec_ref(x_19);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_1);
x_36 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_23);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_free_object(x_33);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_36);
x_40 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_41 = l_Nat_reprFast(x_6);
lean_ctor_set_tag(x_33, 3);
lean_ctor_set(x_33, 0, x_41);
x_42 = l_Lean_MessageData_ofFormat(x_33);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_MessageData_ofExpr(x_7);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_35);
x_50 = l_Lean_MessageData_ofExpr(x_35);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_51, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_35);
return x_52;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_35);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_free_object(x_33);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_35);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_63 = l_Nat_reprFast(x_6);
lean_ctor_set_tag(x_33, 3);
lean_ctor_set(x_33, 0, x_63);
x_64 = l_Lean_MessageData_ofFormat(x_33);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MessageData_ofExpr(x_7);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_35);
x_72 = l_Lean_MessageData_ofExpr(x_35);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_73, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_75 = x_74;
} else {
 lean_dec_ref(x_74);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_35);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_35);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_33, 0);
lean_inc(x_80);
lean_dec(x_33);
lean_inc(x_1);
x_81 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_23);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_unbox(x_82);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_80);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
x_86 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1;
x_87 = l_Nat_reprFast(x_6);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_MessageData_ofFormat(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_MessageData_ofExpr(x_7);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_80);
x_97 = l_Lean_MessageData_ofExpr(x_80);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_98, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_100 = x_99;
} else {
 lean_dec_ref(x_99);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_80);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_80);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_33;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_29;
}
}
else
{
uint8_t x_105; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_27);
if (x_105 == 0)
{
return x_27;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_27, 0);
lean_inc(x_106);
lean_dec(x_27);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
block_154:
{
lean_object* x_117; uint8_t x_118; 
lean_inc(x_1);
x_117 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_1, x_109);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_free_object(x_117);
lean_dec(x_8);
x_18 = x_116;
x_19 = x_113;
x_20 = x_115;
x_21 = x_111;
x_22 = x_112;
x_23 = x_109;
x_24 = x_110;
x_25 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7;
x_122 = l_Nat_reprFast(x_8);
lean_ctor_set_tag(x_117, 3);
lean_ctor_set(x_117, 0, x_122);
x_123 = l_Lean_MessageData_ofFormat(x_117);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_inc_ref(x_113);
x_127 = lean_array_to_list(x_113);
x_128 = lean_box(0);
x_129 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_127, x_128);
x_130 = l_Lean_MessageData_ofList(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_1);
x_132 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_131, x_111, x_112, x_109, x_110);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_18 = x_116;
x_19 = x_113;
x_20 = x_115;
x_21 = x_111;
x_22 = x_112;
x_23 = x_109;
x_24 = x_110;
x_25 = lean_box(0);
goto block_108;
}
else
{
uint8_t x_133; 
lean_dec_ref(x_116);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
return x_132;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_dec(x_8);
x_18 = x_116;
x_19 = x_113;
x_20 = x_115;
x_21 = x_111;
x_22 = x_112;
x_23 = x_109;
x_24 = x_110;
x_25 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_138 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7;
x_139 = l_Nat_reprFast(x_8);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lean_MessageData_ofFormat(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_inc_ref(x_113);
x_145 = lean_array_to_list(x_113);
x_146 = lean_box(0);
x_147 = l_List_mapTR_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__7(x_145, x_146);
x_148 = l_Lean_MessageData_ofList(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_1);
x_150 = l_Lean_addTrace___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__10(x_1, x_149, x_111, x_112, x_109, x_110);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_18 = x_116;
x_19 = x_113;
x_20 = x_115;
x_21 = x_111;
x_22 = x_112;
x_23 = x_109;
x_24 = x_110;
x_25 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_116);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
}
}
block_171:
{
lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_array_mk(x_9);
x_161 = lean_array_size(x_160);
x_162 = 0;
x_163 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__8(x_161, x_162, x_160);
lean_inc(x_8);
x_164 = l_Array_extract___redArg(x_163, x_10, x_8);
lean_inc_ref(x_7);
x_165 = l_Lean_Expr_beta(x_7, x_164);
if (x_11 == 0)
{
x_109 = x_157;
x_110 = x_158;
x_111 = x_155;
x_112 = x_156;
x_113 = x_163;
x_114 = lean_box(0);
x_115 = x_162;
x_116 = x_165;
goto block_154;
}
else
{
if (x_12 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_array_get_size(x_163);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15;
x_170 = l_Lean_Expr_betaRev(x_165, x_169, x_5, x_5);
x_109 = x_157;
x_110 = x_158;
x_111 = x_155;
x_112 = x_156;
x_113 = x_163;
x_114 = lean_box(0);
x_115 = x_162;
x_116 = x_170;
goto block_154;
}
else
{
x_109 = x_157;
x_110 = x_158;
x_111 = x_155;
x_112 = x_156;
x_113 = x_163;
x_114 = lean_box(0);
x_115 = x_162;
x_116 = x_165;
goto block_154;
}
}
else
{
x_109 = x_157;
x_110 = x_158;
x_111 = x_155;
x_112 = x_156;
x_113 = x_163;
x_114 = lean_box(0);
x_115 = x_162;
x_116 = x_165;
goto block_154;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_5);
x_19 = lean_unbox(x_11);
x_20 = lean_unbox(x_12);
x_21 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_19, x_20, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_8, x_16);
if (x_17 == 1)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = l_Lean_Meta_Match_instInhabitedAltLHS_default;
x_20 = lean_array_fget_borrowed(x_7, x_9);
lean_inc(x_9);
x_21 = l_List_get_x21Internal___redArg(x_19, x_1, x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0;
x_24 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_25 = lean_array_get_borrowed(x_16, x_2, x_9);
x_26 = lean_array_get_borrowed(x_23, x_3, x_9);
x_27 = lean_nat_dec_eq(x_25, x_16);
x_28 = lean_box(x_17);
x_29 = lean_box(x_27);
x_30 = lean_box(x_6);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_20);
lean_inc(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_26);
x_31 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___lam__0___boxed), 17, 12);
lean_closure_set(x_31, 0, x_24);
lean_closure_set(x_31, 1, x_26);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_5);
lean_closure_set(x_31, 4, x_28);
lean_closure_set(x_31, 5, x_9);
lean_closure_set(x_31, 6, x_20);
lean_closure_set(x_31, 7, x_25);
lean_closure_set(x_31, 8, x_22);
lean_closure_set(x_31, 9, x_16);
lean_closure_set(x_31, 10, x_29);
lean_closure_set(x_31, 11, x_30);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_32 = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_spec__1___redArg(x_22, x_31, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_8, x_34);
lean_dec(x_8);
x_36 = lean_nat_add(x_9, x_34);
lean_dec(x_9);
x_37 = lean_array_push(x_10, x_33);
x_8 = x_35;
x_9 = x_36;
x_10 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
x_17 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_8, 2);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_49 = 0;
if (x_48 == 0)
{
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = lean_box(0);
goto block_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; uint8_t x_523; 
x_220 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_221 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_IndPredBelow_mkBelow_spec__8___redArg(x_220, x_8);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_224 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___boxed), 8, 2);
lean_closure_set(x_224, 0, x_1);
lean_closure_set(x_224, 1, x_2);
x_225 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__4));
x_523 = lean_unbox(x_222);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; 
x_524 = l_Lean_trace_profiler;
x_525 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_47, x_524);
if (x_525 == 0)
{
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec(x_222);
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = lean_box(0);
goto block_219;
}
else
{
lean_inc_ref(x_47);
goto block_522;
}
}
else
{
lean_inc_ref(x_47);
goto block_522;
}
block_239:
{
lean_object* x_230; double x_231; double x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_230 = lean_io_get_num_heartbeats();
x_231 = lean_float_of_nat(x_227);
x_232 = lean_float_of_nat(x_230);
x_233 = lean_box_float(x_231);
x_234 = lean_box_float(x_232);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_228);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_unbox(x_222);
lean_dec(x_222);
x_238 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_220, x_48, x_225, x_47, x_237, x_226, x_224, x_236, x_6, x_7, x_8, x_9);
lean_dec_ref(x_47);
return x_238;
}
block_245:
{
lean_object* x_244; 
if (lean_is_scalar(x_223)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_223;
 lean_ctor_set_tag(x_244, 1);
}
lean_ctor_set(x_244, 0, x_242);
x_226 = x_240;
x_227 = x_241;
x_228 = x_244;
x_229 = lean_box(0);
goto block_239;
}
block_251:
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_248);
x_226 = x_246;
x_227 = x_247;
x_228 = x_250;
x_229 = lean_box(0);
goto block_239;
}
block_282:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_array_get_size(x_252);
x_267 = lean_mk_empty_array_with_capacity(x_266);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_268 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(x_260, x_256, x_257, x_4, x_5, x_262, x_265, x_252, x_266, x_254, x_267, x_6, x_7, x_8, x_9);
lean_dec_ref(x_252);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_260);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = l_Lean_Expr_app___override(x_258, x_264);
x_272 = l_Lean_mkAppN(x_271, x_261);
lean_dec_ref(x_261);
x_273 = l_Lean_mkAppN(x_272, x_270);
lean_dec(x_270);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_259);
lean_ctor_set_tag(x_268, 1);
lean_ctor_set(x_268, 0, x_274);
x_240 = x_253;
x_241 = x_255;
x_242 = x_268;
x_243 = lean_box(0);
goto block_245;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_275 = lean_ctor_get(x_268, 0);
lean_inc(x_275);
lean_dec(x_268);
x_276 = l_Lean_Expr_app___override(x_258, x_264);
x_277 = l_Lean_mkAppN(x_276, x_261);
lean_dec_ref(x_261);
x_278 = l_Lean_mkAppN(x_277, x_275);
lean_dec(x_275);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_259);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_240 = x_253;
x_241 = x_255;
x_242 = x_280;
x_243 = lean_box(0);
goto block_245;
}
}
else
{
lean_object* x_281; 
lean_dec_ref(x_264);
lean_dec_ref(x_261);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec(x_223);
x_281 = lean_ctor_get(x_268, 0);
lean_inc(x_281);
lean_dec_ref(x_268);
x_246 = x_253;
x_247 = x_255;
x_248 = x_281;
x_249 = lean_box(0);
goto block_251;
}
}
block_299:
{
lean_object* x_287; double x_288; double x_289; double x_290; double x_291; double x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; 
x_287 = lean_io_mono_nanos_now();
x_288 = lean_float_of_nat(x_284);
x_289 = l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
x_290 = lean_float_div(x_288, x_289);
x_291 = lean_float_of_nat(x_287);
x_292 = lean_float_div(x_291, x_289);
x_293 = lean_box_float(x_290);
x_294 = lean_box_float(x_292);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_unbox(x_222);
lean_dec(x_222);
x_298 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg(x_220, x_48, x_225, x_47, x_297, x_283, x_224, x_296, x_6, x_7, x_8, x_9);
lean_dec_ref(x_47);
return x_298;
}
block_305:
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_302);
x_283 = x_300;
x_284 = x_301;
x_285 = x_304;
x_286 = lean_box(0);
goto block_299;
}
block_311:
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_308);
x_283 = x_306;
x_284 = x_307;
x_285 = x_310;
x_286 = lean_box(0);
goto block_299;
}
block_341:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_array_get_size(x_313);
x_326 = lean_mk_empty_array_with_capacity(x_325);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_327 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(x_323, x_321, x_320, x_4, x_5, x_48, x_324, x_313, x_325, x_316, x_326, x_6, x_7, x_8, x_9);
lean_dec_ref(x_313);
lean_dec_ref(x_320);
lean_dec_ref(x_321);
lean_dec(x_323);
if (lean_obj_tag(x_327) == 0)
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_327, 0);
x_330 = l_Lean_Expr_app___override(x_317, x_319);
x_331 = l_Lean_mkAppN(x_330, x_322);
lean_dec_ref(x_322);
x_332 = l_Lean_mkAppN(x_331, x_329);
lean_dec(x_329);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_312);
lean_ctor_set_tag(x_327, 1);
lean_ctor_set(x_327, 0, x_333);
x_300 = x_315;
x_301 = x_318;
x_302 = x_327;
x_303 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_334 = lean_ctor_get(x_327, 0);
lean_inc(x_334);
lean_dec(x_327);
x_335 = l_Lean_Expr_app___override(x_317, x_319);
x_336 = l_Lean_mkAppN(x_335, x_322);
lean_dec_ref(x_322);
x_337 = l_Lean_mkAppN(x_336, x_334);
lean_dec(x_334);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_312);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_300 = x_315;
x_301 = x_318;
x_302 = x_339;
x_303 = lean_box(0);
goto block_305;
}
}
else
{
lean_object* x_340; 
lean_dec_ref(x_322);
lean_dec_ref(x_319);
lean_dec_ref(x_317);
lean_dec_ref(x_312);
x_340 = lean_ctor_get(x_327, 0);
lean_inc(x_340);
lean_dec_ref(x_327);
x_306 = x_315;
x_307 = x_318;
x_308 = x_340;
x_309 = lean_box(0);
goto block_311;
}
}
block_522:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_342 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg(x_9);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = l_Lean_trace_profiler_useHeartbeats;
x_345 = l_Lean_Option_get___at___00Lean_Meta_IndPredBelow_mkBelow_spec__10(x_47, x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_223);
x_346 = lean_io_mono_nanos_now();
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_347 = l_Lean_Meta_Match_getMkMatcherInputInContext(x_1, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; size_t x_357; size_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec_ref(x_347);
x_349 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_349);
x_350 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_350);
x_351 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_351);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_348, 3);
x_353 = lean_unsigned_to_nat(0u);
x_354 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0;
x_355 = lean_array_get_size(x_350);
lean_inc(x_352);
x_356 = lean_array_mk(x_352);
x_357 = lean_array_size(x_356);
x_358 = 0;
x_359 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(x_357, x_358, x_356);
x_360 = lean_array_get_size(x_359);
x_361 = lean_mk_array(x_360, x_354);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_354);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_348);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_355);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_350);
lean_ctor_set(x_365, 1, x_364);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_366 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(x_4, x_2, x_3, x_365, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = lean_ctor_get(x_367, 1);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 0);
lean_inc(x_371);
lean_dec(x_367);
x_372 = lean_ctor_get(x_369, 0);
lean_inc(x_372);
lean_dec(x_369);
x_373 = lean_ctor_get(x_370, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_370, 1);
lean_inc(x_374);
lean_dec(x_370);
x_375 = l_Array_isEmpty___redArg(x_373);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_372, 1);
lean_inc_ref(x_377);
x_378 = lean_ctor_get(x_372, 2);
lean_inc_ref(x_378);
x_379 = lean_ctor_get(x_372, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_372, 4);
lean_inc(x_380);
lean_dec(x_372);
x_381 = lean_box(x_49);
x_382 = lean_box(x_48);
lean_inc(x_373);
lean_inc_ref(x_2);
x_383 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__6___boxed), 16, 9);
lean_closure_set(x_383, 0, x_381);
lean_closure_set(x_383, 1, x_382);
lean_closure_set(x_383, 2, x_2);
lean_closure_set(x_383, 3, x_373);
lean_closure_set(x_383, 4, x_353);
lean_closure_set(x_383, 5, x_376);
lean_closure_set(x_383, 6, x_378);
lean_closure_set(x_383, 7, x_379);
lean_closure_set(x_383, 8, x_380);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_384 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_377, x_383, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
x_386 = lean_box(x_49);
x_387 = lean_box(x_48);
x_388 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__8___boxed), 12, 5);
lean_closure_set(x_388, 0, x_386);
lean_closure_set(x_388, 1, x_387);
lean_closure_set(x_388, 2, x_2);
lean_closure_set(x_388, 3, x_373);
lean_closure_set(x_388, 4, x_353);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_389 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_349, x_388, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1));
x_392 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_391, x_9);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
x_394 = !lean_is_exclusive(x_385);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_ctor_get(x_385, 2);
x_396 = lean_ctor_get(x_385, 3);
x_397 = lean_ctor_get(x_385, 0);
lean_dec(x_397);
lean_inc(x_396);
lean_inc_ref(x_395);
lean_ctor_set(x_385, 0, x_393);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_398 = l_Lean_Meta_Match_mkMatcher(x_385, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = lean_ctor_get(x_399, 0);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_399, 3);
lean_inc_ref(x_401);
lean_dec(x_399);
lean_inc_ref(x_401);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_402 = lean_apply_5(x_401, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
lean_dec_ref(x_402);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_400);
x_403 = l_Lean_Meta_check(x_400, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; uint8_t x_405; 
lean_dec_ref(x_403);
x_404 = lean_array_get_size(x_395);
x_405 = lean_nat_dec_lt(x_353, x_404);
if (x_405 == 0)
{
lean_dec_ref(x_395);
x_312 = x_401;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_400;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_396;
x_324 = x_345;
goto block_341;
}
else
{
if (x_405 == 0)
{
lean_dec_ref(x_395);
x_312 = x_401;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_400;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_396;
x_324 = x_345;
goto block_341;
}
else
{
size_t x_406; uint8_t x_407; 
x_406 = lean_usize_of_nat(x_404);
x_407 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(x_345, x_48, x_395, x_358, x_406);
lean_dec_ref(x_395);
x_312 = x_401;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_400;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_396;
x_324 = x_407;
goto block_341;
}
}
}
else
{
lean_object* x_408; 
lean_dec_ref(x_401);
lean_dec_ref(x_400);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_408 = lean_ctor_get(x_403, 0);
lean_inc(x_408);
lean_dec_ref(x_403);
x_306 = x_343;
x_307 = x_346;
x_308 = x_408;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_409; 
lean_dec_ref(x_401);
lean_dec_ref(x_400);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_409 = lean_ctor_get(x_402, 0);
lean_inc(x_409);
lean_dec_ref(x_402);
x_306 = x_343;
x_307 = x_346;
x_308 = x_409;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_410; 
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_410 = lean_ctor_get(x_398, 0);
lean_inc(x_410);
lean_dec_ref(x_398);
x_306 = x_343;
x_307 = x_346;
x_308 = x_410;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_ctor_get(x_385, 1);
x_412 = lean_ctor_get(x_385, 2);
x_413 = lean_ctor_get(x_385, 3);
x_414 = lean_ctor_get(x_385, 4);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_385);
lean_inc(x_413);
lean_inc_ref(x_412);
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_393);
lean_ctor_set(x_415, 1, x_411);
lean_ctor_set(x_415, 2, x_412);
lean_ctor_set(x_415, 3, x_413);
lean_ctor_set(x_415, 4, x_414);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_416 = l_Lean_Meta_Match_mkMatcher(x_415, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_ctor_get(x_417, 0);
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_417, 3);
lean_inc_ref(x_419);
lean_dec(x_417);
lean_inc_ref(x_419);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_420 = lean_apply_5(x_419, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
lean_dec_ref(x_420);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_418);
x_421 = l_Lean_Meta_check(x_418, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; uint8_t x_423; 
lean_dec_ref(x_421);
x_422 = lean_array_get_size(x_412);
x_423 = lean_nat_dec_lt(x_353, x_422);
if (x_423 == 0)
{
lean_dec_ref(x_412);
x_312 = x_419;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_418;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_413;
x_324 = x_345;
goto block_341;
}
else
{
if (x_423 == 0)
{
lean_dec_ref(x_412);
x_312 = x_419;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_418;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_413;
x_324 = x_345;
goto block_341;
}
else
{
size_t x_424; uint8_t x_425; 
x_424 = lean_usize_of_nat(x_422);
x_425 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(x_345, x_48, x_412, x_358, x_424);
lean_dec_ref(x_412);
x_312 = x_419;
x_313 = x_351;
x_314 = lean_box(0);
x_315 = x_343;
x_316 = x_353;
x_317 = x_418;
x_318 = x_346;
x_319 = x_390;
x_320 = x_374;
x_321 = x_359;
x_322 = x_371;
x_323 = x_413;
x_324 = x_425;
goto block_341;
}
}
}
else
{
lean_object* x_426; 
lean_dec_ref(x_419);
lean_dec_ref(x_418);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_426 = lean_ctor_get(x_421, 0);
lean_inc(x_426);
lean_dec_ref(x_421);
x_306 = x_343;
x_307 = x_346;
x_308 = x_426;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_427; 
lean_dec_ref(x_419);
lean_dec_ref(x_418);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_427 = lean_ctor_get(x_420, 0);
lean_inc(x_427);
lean_dec_ref(x_420);
x_306 = x_343;
x_307 = x_346;
x_308 = x_427;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_428; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_390);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_428 = lean_ctor_get(x_416, 0);
lean_inc(x_428);
lean_dec_ref(x_416);
x_306 = x_343;
x_307 = x_346;
x_308 = x_428;
x_309 = lean_box(0);
goto block_311;
}
}
}
else
{
lean_object* x_429; 
lean_dec(x_385);
lean_dec(x_374);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_429 = lean_ctor_get(x_389, 0);
lean_inc(x_429);
lean_dec_ref(x_389);
x_306 = x_343;
x_307 = x_346;
x_308 = x_429;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_430; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_349);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_430 = lean_ctor_get(x_384, 0);
lean_inc(x_430);
lean_dec_ref(x_384);
x_306 = x_343;
x_307 = x_346;
x_308 = x_430;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_431; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_349);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_431 = lean_box(0);
x_300 = x_343;
x_301 = x_346;
x_302 = x_431;
x_303 = lean_box(0);
goto block_305;
}
}
else
{
lean_object* x_432; 
lean_dec_ref(x_359);
lean_dec_ref(x_351);
lean_dec_ref(x_349);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_432 = lean_ctor_get(x_366, 0);
lean_inc(x_432);
lean_dec_ref(x_366);
x_306 = x_343;
x_307 = x_346;
x_308 = x_432;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_433; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_433 = lean_ctor_get(x_347, 0);
lean_inc(x_433);
lean_dec_ref(x_347);
x_306 = x_343;
x_307 = x_346;
x_308 = x_433;
x_309 = lean_box(0);
goto block_311;
}
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_io_get_num_heartbeats();
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_435 = l_Lean_Meta_Match_getMkMatcherInputInContext(x_1, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; size_t x_445; size_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
x_437 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_437);
x_438 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_438);
x_439 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_439);
lean_dec_ref(x_1);
x_440 = lean_ctor_get(x_436, 3);
x_441 = lean_unsigned_to_nat(0u);
x_442 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0;
x_443 = lean_array_get_size(x_438);
lean_inc(x_440);
x_444 = lean_array_mk(x_440);
x_445 = lean_array_size(x_444);
x_446 = 0;
x_447 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(x_445, x_446, x_444);
x_448 = lean_array_get_size(x_447);
x_449 = lean_mk_array(x_448, x_442);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_442);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_436);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_443);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_438);
lean_ctor_set(x_453, 1, x_452);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_454 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(x_4, x_2, x_3, x_453, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec_ref(x_454);
x_456 = lean_ctor_get(x_455, 1);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
lean_dec(x_455);
x_460 = lean_ctor_get(x_457, 0);
lean_inc(x_460);
lean_dec(x_457);
x_461 = lean_ctor_get(x_458, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_458, 1);
lean_inc(x_462);
lean_dec(x_458);
x_463 = l_Array_isEmpty___redArg(x_461);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_464 = lean_ctor_get(x_460, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_460, 1);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_460, 2);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_460, 3);
lean_inc(x_467);
x_468 = lean_ctor_get(x_460, 4);
lean_inc(x_468);
lean_dec(x_460);
x_469 = lean_box(x_49);
x_470 = lean_box(x_345);
lean_inc(x_461);
lean_inc_ref(x_2);
x_471 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__10___boxed), 16, 9);
lean_closure_set(x_471, 0, x_469);
lean_closure_set(x_471, 1, x_470);
lean_closure_set(x_471, 2, x_2);
lean_closure_set(x_471, 3, x_461);
lean_closure_set(x_471, 4, x_441);
lean_closure_set(x_471, 5, x_464);
lean_closure_set(x_471, 6, x_466);
lean_closure_set(x_471, 7, x_467);
lean_closure_set(x_471, 8, x_468);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_472 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_465, x_471, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
lean_dec_ref(x_472);
x_474 = lean_box(x_49);
x_475 = lean_box(x_345);
x_476 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__12___boxed), 12, 5);
lean_closure_set(x_476, 0, x_474);
lean_closure_set(x_476, 1, x_475);
lean_closure_set(x_476, 2, x_2);
lean_closure_set(x_476, 3, x_461);
lean_closure_set(x_476, 4, x_441);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_477 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_437, x_476, x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
lean_dec_ref(x_477);
x_479 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1));
x_480 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_479, x_9);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec_ref(x_480);
x_482 = !lean_is_exclusive(x_473);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_483 = lean_ctor_get(x_473, 2);
x_484 = lean_ctor_get(x_473, 3);
x_485 = lean_ctor_get(x_473, 0);
lean_dec(x_485);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_ctor_set(x_473, 0, x_481);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_486 = l_Lean_Meta_Match_mkMatcher(x_473, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc_ref(x_488);
x_489 = lean_ctor_get(x_487, 3);
lean_inc_ref(x_489);
lean_dec(x_487);
lean_inc_ref(x_489);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_490 = lean_apply_5(x_489, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
lean_dec_ref(x_490);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_488);
x_491 = l_Lean_Meta_check(x_488, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; uint8_t x_493; 
lean_dec_ref(x_491);
x_492 = lean_array_get_size(x_483);
x_493 = lean_nat_dec_lt(x_441, x_492);
if (x_493 == 0)
{
lean_dec_ref(x_483);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_488;
x_259 = x_489;
x_260 = x_484;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_463;
goto block_282;
}
else
{
if (x_493 == 0)
{
lean_dec_ref(x_483);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_488;
x_259 = x_489;
x_260 = x_484;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_463;
goto block_282;
}
else
{
size_t x_494; uint8_t x_495; 
x_494 = lean_usize_of_nat(x_492);
x_495 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(x_463, x_345, x_483, x_446, x_494);
lean_dec_ref(x_483);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_488;
x_259 = x_489;
x_260 = x_484;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_495;
goto block_282;
}
}
}
else
{
lean_object* x_496; 
lean_dec_ref(x_489);
lean_dec_ref(x_488);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_496 = lean_ctor_get(x_491, 0);
lean_inc(x_496);
lean_dec_ref(x_491);
x_246 = x_343;
x_247 = x_434;
x_248 = x_496;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_497; 
lean_dec_ref(x_489);
lean_dec_ref(x_488);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_497 = lean_ctor_get(x_490, 0);
lean_inc(x_497);
lean_dec_ref(x_490);
x_246 = x_343;
x_247 = x_434;
x_248 = x_497;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_498; 
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_498 = lean_ctor_get(x_486, 0);
lean_inc(x_498);
lean_dec_ref(x_486);
x_246 = x_343;
x_247 = x_434;
x_248 = x_498;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_499 = lean_ctor_get(x_473, 1);
x_500 = lean_ctor_get(x_473, 2);
x_501 = lean_ctor_get(x_473, 3);
x_502 = lean_ctor_get(x_473, 4);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_473);
lean_inc(x_501);
lean_inc_ref(x_500);
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_481);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
lean_ctor_set(x_503, 4, x_502);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_504 = l_Lean_Meta_Match_mkMatcher(x_503, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = lean_ctor_get(x_505, 0);
lean_inc_ref(x_506);
x_507 = lean_ctor_get(x_505, 3);
lean_inc_ref(x_507);
lean_dec(x_505);
lean_inc_ref(x_507);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_508 = lean_apply_5(x_507, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
lean_dec_ref(x_508);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_506);
x_509 = l_Lean_Meta_check(x_506, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; uint8_t x_511; 
lean_dec_ref(x_509);
x_510 = lean_array_get_size(x_500);
x_511 = lean_nat_dec_lt(x_441, x_510);
if (x_511 == 0)
{
lean_dec_ref(x_500);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_506;
x_259 = x_507;
x_260 = x_501;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_463;
goto block_282;
}
else
{
if (x_511 == 0)
{
lean_dec_ref(x_500);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_506;
x_259 = x_507;
x_260 = x_501;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_463;
goto block_282;
}
else
{
size_t x_512; uint8_t x_513; 
x_512 = lean_usize_of_nat(x_510);
x_513 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__15(x_463, x_345, x_500, x_446, x_512);
lean_dec_ref(x_500);
x_252 = x_439;
x_253 = x_343;
x_254 = x_441;
x_255 = x_434;
x_256 = x_447;
x_257 = x_462;
x_258 = x_506;
x_259 = x_507;
x_260 = x_501;
x_261 = x_459;
x_262 = x_345;
x_263 = lean_box(0);
x_264 = x_478;
x_265 = x_513;
goto block_282;
}
}
}
else
{
lean_object* x_514; 
lean_dec_ref(x_507);
lean_dec_ref(x_506);
lean_dec(x_501);
lean_dec_ref(x_500);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_514 = lean_ctor_get(x_509, 0);
lean_inc(x_514);
lean_dec_ref(x_509);
x_246 = x_343;
x_247 = x_434;
x_248 = x_514;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_515; 
lean_dec_ref(x_507);
lean_dec_ref(x_506);
lean_dec(x_501);
lean_dec_ref(x_500);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_515 = lean_ctor_get(x_508, 0);
lean_inc(x_515);
lean_dec_ref(x_508);
x_246 = x_343;
x_247 = x_434;
x_248 = x_515;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_516; 
lean_dec(x_501);
lean_dec_ref(x_500);
lean_dec(x_478);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_516 = lean_ctor_get(x_504, 0);
lean_inc(x_516);
lean_dec_ref(x_504);
x_246 = x_343;
x_247 = x_434;
x_248 = x_516;
x_249 = lean_box(0);
goto block_251;
}
}
}
else
{
lean_object* x_517; 
lean_dec(x_473);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_517 = lean_ctor_get(x_477, 0);
lean_inc(x_517);
lean_dec_ref(x_477);
x_246 = x_343;
x_247 = x_434;
x_248 = x_517;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_518; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec_ref(x_437);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_518 = lean_ctor_get(x_472, 0);
lean_inc(x_518);
lean_dec_ref(x_472);
x_246 = x_343;
x_247 = x_434;
x_248 = x_518;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_519; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec_ref(x_437);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_519 = lean_box(0);
x_240 = x_343;
x_241 = x_434;
x_242 = x_519;
x_243 = lean_box(0);
goto block_245;
}
}
else
{
lean_object* x_520; 
lean_dec_ref(x_447);
lean_dec_ref(x_439);
lean_dec_ref(x_437);
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_520 = lean_ctor_get(x_454, 0);
lean_inc(x_520);
lean_dec_ref(x_454);
x_246 = x_343;
x_247 = x_434;
x_248 = x_520;
x_249 = lean_box(0);
goto block_251;
}
}
else
{
lean_object* x_521; 
lean_dec(x_223);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_435, 0);
lean_inc(x_521);
lean_dec_ref(x_435);
x_246 = x_343;
x_247 = x_434;
x_248 = x_521;
x_249 = lean_box(0);
goto block_251;
}
}
}
}
block_46:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_array_get_size(x_13);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg(x_24, x_18, x_21, x_4, x_5, x_25, x_13, x_26, x_11, x_27, x_20, x_15, x_22, x_12);
lean_dec_ref(x_13);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_Expr_app___override(x_19, x_14);
x_32 = l_Lean_mkAppN(x_31, x_16);
lean_dec_ref(x_16);
x_33 = l_Lean_mkAppN(x_32, x_30);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = l_Lean_Expr_app___override(x_19, x_14);
x_38 = l_Lean_mkAppN(x_37, x_16);
lean_dec_ref(x_16);
x_39 = l_Lean_mkAppN(x_38, x_36);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
block_219:
{
lean_object* x_55; 
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_1);
x_55 = l_Lean_Meta_Match_getMkMatcherInputInContext(x_1, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_59);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_56, 3);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0;
x_63 = lean_array_get_size(x_58);
lean_inc(x_60);
x_64 = lean_array_mk(x_60);
x_65 = lean_array_size(x_64);
x_66 = 0;
x_67 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__4(x_65, x_66, x_64);
x_68 = lean_array_get_size(x_67);
x_69 = lean_mk_array(x_68, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_58);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_2);
x_74 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5(x_4, x_2, x_3, x_73, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_76, 1);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = l_Array_isEmpty___redArg(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_74);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_81, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_81, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 4);
lean_inc(x_89);
lean_dec(x_81);
x_90 = lean_box(x_49);
lean_inc(x_82);
lean_inc_ref(x_2);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1___boxed), 15, 8);
lean_closure_set(x_91, 0, x_90);
lean_closure_set(x_91, 1, x_2);
lean_closure_set(x_91, 2, x_82);
lean_closure_set(x_91, 3, x_61);
lean_closure_set(x_91, 4, x_85);
lean_closure_set(x_91, 5, x_87);
lean_closure_set(x_91, 6, x_88);
lean_closure_set(x_91, 7, x_89);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_92 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_86, x_91, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_box(x_49);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3___boxed), 11, 4);
lean_closure_set(x_95, 0, x_94);
lean_closure_set(x_95, 1, x_2);
lean_closure_set(x_95, 2, x_82);
lean_closure_set(x_95, 3, x_61);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_96 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_57, x_95, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1));
x_99 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_98, x_53);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = !lean_is_exclusive(x_93);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_93, 2);
x_103 = lean_ctor_get(x_93, 3);
x_104 = lean_ctor_get(x_93, 0);
lean_dec(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_ctor_set(x_93, 0, x_100);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_105 = l_Lean_Meta_Match_mkMatcher(x_93, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_108);
lean_dec(x_106);
lean_inc_ref(x_108);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_109 = lean_apply_5(x_108, x_50, x_51, x_52, x_53, lean_box(0));
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec_ref(x_109);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_107);
x_110 = l_Lean_Meta_check(x_107, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_dec_ref(x_110);
x_111 = lean_array_get_size(x_102);
x_112 = lean_nat_dec_lt(x_61, x_111);
if (x_112 == 0)
{
lean_dec_ref(x_102);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_108;
x_18 = x_67;
x_19 = x_107;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_103;
x_25 = x_84;
goto block_46;
}
else
{
if (x_112 == 0)
{
lean_dec_ref(x_102);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_108;
x_18 = x_67;
x_19 = x_107;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_103;
x_25 = x_84;
goto block_46;
}
else
{
size_t x_113; uint8_t x_114; 
x_113 = lean_usize_of_nat(x_111);
x_114 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(x_84, x_102, x_66, x_113);
lean_dec_ref(x_102);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_108;
x_18 = x_67;
x_19 = x_107;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_103;
x_25 = x_114;
goto block_46;
}
}
}
else
{
uint8_t x_115; 
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
return x_109;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
lean_dec(x_109);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_121 = !lean_is_exclusive(x_105);
if (x_121 == 0)
{
return x_105;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_105, 0);
lean_inc(x_122);
lean_dec(x_105);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_93, 1);
x_125 = lean_ctor_get(x_93, 2);
x_126 = lean_ctor_get(x_93, 3);
x_127 = lean_ctor_get(x_93, 4);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_93);
lean_inc(x_126);
lean_inc_ref(x_125);
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_100);
lean_ctor_set(x_128, 1, x_124);
lean_ctor_set(x_128, 2, x_125);
lean_ctor_set(x_128, 3, x_126);
lean_ctor_set(x_128, 4, x_127);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_129 = l_Lean_Meta_Match_mkMatcher(x_128, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_130, 3);
lean_inc_ref(x_132);
lean_dec(x_130);
lean_inc_ref(x_132);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_133 = lean_apply_5(x_132, x_50, x_51, x_52, x_53, lean_box(0));
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_dec_ref(x_133);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_131);
x_134 = l_Lean_Meta_check(x_131, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
lean_dec_ref(x_134);
x_135 = lean_array_get_size(x_125);
x_136 = lean_nat_dec_lt(x_61, x_135);
if (x_136 == 0)
{
lean_dec_ref(x_125);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_132;
x_18 = x_67;
x_19 = x_131;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_126;
x_25 = x_84;
goto block_46;
}
else
{
if (x_136 == 0)
{
lean_dec_ref(x_125);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_132;
x_18 = x_67;
x_19 = x_131;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_126;
x_25 = x_84;
goto block_46;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_usize_of_nat(x_135);
x_138 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(x_84, x_125, x_66, x_137);
lean_dec_ref(x_125);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_97;
x_15 = x_51;
x_16 = x_80;
x_17 = x_132;
x_18 = x_67;
x_19 = x_131;
x_20 = x_50;
x_21 = x_83;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_126;
x_25 = x_138;
goto block_46;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_140 = x_134;
} else {
 lean_dec_ref(x_134);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_143 = x_133;
} else {
 lean_dec_ref(x_133);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_145 = lean_ctor_get(x_129, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_146 = x_129;
} else {
 lean_dec_ref(x_129);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_93);
lean_dec(x_83);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_148 = !lean_is_exclusive(x_96);
if (x_148 == 0)
{
return x_96;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_96, 0);
lean_inc(x_149);
lean_dec(x_96);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_151 = !lean_is_exclusive(x_92);
if (x_151 == 0)
{
return x_92;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_92, 0);
lean_inc(x_152);
lean_dec(x_92);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_154 = lean_box(0);
lean_ctor_set(x_74, 0, x_154);
return x_74;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_155 = lean_ctor_get(x_74, 0);
lean_inc(x_155);
lean_dec(x_74);
x_156 = lean_ctor_get(x_155, 1);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
lean_dec(x_155);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = l_Array_isEmpty___redArg(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 1);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_160, 2);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_160, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 4);
lean_inc(x_168);
lean_dec(x_160);
x_169 = lean_box(x_49);
lean_inc(x_161);
lean_inc_ref(x_2);
x_170 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__1___boxed), 15, 8);
lean_closure_set(x_170, 0, x_169);
lean_closure_set(x_170, 1, x_2);
lean_closure_set(x_170, 2, x_161);
lean_closure_set(x_170, 3, x_61);
lean_closure_set(x_170, 4, x_164);
lean_closure_set(x_170, 5, x_166);
lean_closure_set(x_170, 6, x_167);
lean_closure_set(x_170, 7, x_168);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_171 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive_spec__0___redArg(x_165, x_170, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = lean_box(x_49);
x_174 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__3___boxed), 11, 4);
lean_closure_set(x_174, 0, x_173);
lean_closure_set(x_174, 1, x_2);
lean_closure_set(x_174, 2, x_161);
lean_closure_set(x_174, 3, x_61);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_175 = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__6___redArg(x_57, x_174, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1));
x_178 = l_Lean_mkAuxDeclName___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__7___redArg(x_177, x_53);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = lean_ctor_get(x_172, 1);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_172, 2);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_172, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 4);
lean_inc(x_183);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 x_184 = x_172;
} else {
 lean_dec_ref(x_172);
 x_184 = lean_box(0);
}
lean_inc(x_182);
lean_inc_ref(x_181);
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_179);
lean_ctor_set(x_185, 1, x_180);
lean_ctor_set(x_185, 2, x_181);
lean_ctor_set(x_185, 3, x_182);
lean_ctor_set(x_185, 4, x_183);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_186 = l_Lean_Meta_Match_mkMatcher(x_185, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_187, 3);
lean_inc_ref(x_189);
lean_dec(x_187);
lean_inc_ref(x_189);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
x_190 = lean_apply_5(x_189, x_50, x_51, x_52, x_53, lean_box(0));
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
lean_dec_ref(x_190);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_188);
x_191 = l_Lean_Meta_check(x_188, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; uint8_t x_193; 
lean_dec_ref(x_191);
x_192 = lean_array_get_size(x_181);
x_193 = lean_nat_dec_lt(x_61, x_192);
if (x_193 == 0)
{
lean_dec_ref(x_181);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_176;
x_15 = x_51;
x_16 = x_159;
x_17 = x_189;
x_18 = x_67;
x_19 = x_188;
x_20 = x_50;
x_21 = x_162;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_182;
x_25 = x_163;
goto block_46;
}
else
{
if (x_193 == 0)
{
lean_dec_ref(x_181);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_176;
x_15 = x_51;
x_16 = x_159;
x_17 = x_189;
x_18 = x_67;
x_19 = x_188;
x_20 = x_50;
x_21 = x_162;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_182;
x_25 = x_163;
goto block_46;
}
else
{
size_t x_194; uint8_t x_195; 
x_194 = lean_usize_of_nat(x_192);
x_195 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__13(x_163, x_181, x_66, x_194);
lean_dec_ref(x_181);
x_11 = x_61;
x_12 = x_53;
x_13 = x_59;
x_14 = x_176;
x_15 = x_51;
x_16 = x_159;
x_17 = x_189;
x_18 = x_67;
x_19 = x_188;
x_20 = x_50;
x_21 = x_162;
x_22 = x_52;
x_23 = lean_box(0);
x_24 = x_182;
x_25 = x_195;
goto block_46;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_196 = lean_ctor_get(x_191, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_197 = x_191;
} else {
 lean_dec_ref(x_191);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_199 = lean_ctor_get(x_190, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_200 = x_190;
} else {
 lean_dec_ref(x_190);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_202 = lean_ctor_get(x_186, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_203 = x_186;
} else {
 lean_dec_ref(x_186);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_172);
lean_dec(x_162);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
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
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_208 = lean_ctor_get(x_171, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_209 = x_171;
} else {
 lean_dec_ref(x_171);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec_ref(x_67);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_213 = !lean_is_exclusive(x_74);
if (x_213 == 0)
{
return x_74;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_74, 0);
lean_inc(x_214);
lean_dec(x_74);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_216 = !lean_is_exclusive(x_55);
if (x_216 == 0)
{
return x_55;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_55, 0);
lean_inc(x_217);
lean_dec(x_55);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
x_18 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__12(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___boxed(lean_object** _args) {
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
x_18 = lean_unbox(x_6);
x_19 = lean_unbox(x_7);
x_20 = l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_20;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3441964792u);
x_2 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__16_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__18_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__20_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Meta_IndPredBelow_mkBelow___closed__3));
x_3 = 0;
x_4 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__2));
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_4);
return x_7;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_IndPredBelow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType_spec__0___redArg___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_ihTypeToBelowType___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductive___closed__0);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__0);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowInductives___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_withBRecOnArgs_go_spec__0___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_IndPredBelow_mkBelow_spec__9___redArg___closed__2);
l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0 = _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0();
lean_mark_persistent(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1_spec__2___closed__0);
l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1 = _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__1);
l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3 = _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__3);
l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6 = _init_l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6();
lean_mark_persistent(l_Lean_getConstInfoRec___at___00Lean_Meta_IndPredBelow_mkBelow_spec__1___closed__6);
l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1 = _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___at___00Lean_Meta_IndPredBelow_mkBelow_spec__0___closed__1);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__0();
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__2);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_IndPredBelow_mkBelow_spec__11___redArg___closed__3();
l_Lean_Meta_IndPredBelow_mkBelow___closed__5 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5();
l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0 = _init_l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowRecIndices_spec__2___closed__0);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__2);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__2___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__2);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataRecursionContext___lam__6___closed__16);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___lam__0___closed__6);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_instToMessageDataNewDecl);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_collectDirectVarsInPattern___closed__0);
l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1 = _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType_spec__0___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_toBelowType___lam__0___closed__0);
l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__3___redArg___closed__0);
l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1 = _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__1);
l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3 = _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3();
lean_mark_persistent(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__0___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__1___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lam__3___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_spec__4___closed__4);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lam__1___closed__1);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0 = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___closed__0);
l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lam__4___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__5___closed__0);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__1);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__3);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__5);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__7);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__9);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__13);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__14);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__15);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___lam__0___closed__17);
l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0 = _init_l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lean_Meta_IndPredBelow_mkBelowMatcher_spec__14___redArg___closed__0);
l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__0);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__17_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__19_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__21_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_);
l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn___closed__22_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_initFn_00___x40_Lean_Meta_IndPredBelow_3441964792____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
