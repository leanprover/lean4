// Lean compiler output
// Module: Lean.Meta.CtorIdxHInj
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Refl import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Tactic.Subst
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
static const lean_string_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hinj"};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0 = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x'"};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 12, 207, 74, 240, 119, 195, 119)}};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object* v_indName_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = l_Lean_mkCtorIdxName(v_indName_3_);
v___x_5_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6_ = l_Lean_Name_str___override(v___x_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(lean_object* v_mvarId_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v_mvarId_7_);
v___x_13_ = l_Lean_MVarId_getType(v_mvarId_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; uint8_t v___x_15_; uint8_t v___x_16_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = l_Lean_Expr_isForall(v_a_14_);
lean_dec(v_a_14_);
v___x_16_ = 1;
if (v___x_15_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_MVarId_refl(v_mvarId_7_, v___x_16_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
return v___x_17_;
}
else
{
uint8_t v___x_18_; lean_object* v___x_19_; 
v___x_18_ = 0;
v___x_19_ = l_Lean_Meta_intro1Core(v_mvarId_7_, v___x_18_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_fst_21_; lean_object* v_snd_22_; lean_object* v___x_23_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_19_, 1);
v_fst_21_ = lean_ctor_get(v_a_20_, 0);
lean_inc(v_fst_21_);
v_snd_22_ = lean_ctor_get(v_a_20_, 1);
lean_inc(v_snd_22_);
lean_dec(v_a_20_);
v___x_23_ = l_Lean_Meta_heqToEq(v_snd_22_, v_fst_21_, v___x_16_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_23_, 1);
v_fst_25_ = lean_ctor_get(v_a_24_, 0);
lean_inc(v_fst_25_);
v_snd_26_ = lean_ctor_get(v_a_24_, 1);
lean_inc(v_snd_26_);
lean_dec(v_a_24_);
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_Meta_substEq(v_snd_26_, v_fst_25_, v___x_27_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_snd_30_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_28_, 1);
v_snd_30_ = lean_ctor_get(v_a_29_, 1);
lean_inc(v_snd_30_);
lean_dec(v_a_29_);
v_mvarId_7_ = v_snd_30_;
goto _start;
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_28_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_28_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_23_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_23_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_19_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_19_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec(v_mvarId_7_);
v_a_56_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_13_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_13_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl___boxed(lean_object* v_mvarId_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_mvarId_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(lean_object* v_xs_71_, lean_object* v_k_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(lean_box(0), v_xs_71_, v_k_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg___boxed(lean_object* v_xs_95_, lean_object* v_k_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_95_, v_k_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(lean_object* v_00_u03b1_103_, lean_object* v_xs_104_, lean_object* v_k_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_104_, v_k_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed(lean_object* v_00_u03b1_112_, lean_object* v_xs_113_, lean_object* v_k_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(v_00_u03b1_112_, v_xs_113_, v_k_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(lean_object* v_k_121_, lean_object* v_b_122_, lean_object* v_c_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; 
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
v___x_129_ = lean_apply_7(v_k_121_, v_b_122_, v_c_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed(lean_object* v_k_130_, lean_object* v_b_131_, lean_object* v_c_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(v_k_130_, v_b_131_, v_c_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(lean_object* v_type_139_, lean_object* v_maxFVars_x3f_140_, lean_object* v_k_141_, uint8_t v_cleanupAnnotations_142_, uint8_t v_whnfType_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_149_, 0, v_k_141_);
v___x_150_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_139_, v_maxFVars_x3f_140_, v___f_149_, v_cleanupAnnotations_142_, v_whnfType_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___boxed(lean_object* v_type_167_, lean_object* v_maxFVars_x3f_168_, lean_object* v_k_169_, lean_object* v_cleanupAnnotations_170_, lean_object* v_whnfType_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_177_; uint8_t v_whnfType_boxed_178_; lean_object* v_res_179_; 
v_cleanupAnnotations_boxed_177_ = lean_unbox(v_cleanupAnnotations_170_);
v_whnfType_boxed_178_ = lean_unbox(v_whnfType_171_);
v_res_179_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_167_, v_maxFVars_x3f_168_, v_k_169_, v_cleanupAnnotations_boxed_177_, v_whnfType_boxed_178_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(lean_object* v_00_u03b1_180_, lean_object* v_type_181_, lean_object* v_maxFVars_x3f_182_, lean_object* v_k_183_, uint8_t v_cleanupAnnotations_184_, uint8_t v_whnfType_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_181_, v_maxFVars_x3f_182_, v_k_183_, v_cleanupAnnotations_184_, v_whnfType_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___boxed(lean_object* v_00_u03b1_192_, lean_object* v_type_193_, lean_object* v_maxFVars_x3f_194_, lean_object* v_k_195_, lean_object* v_cleanupAnnotations_196_, lean_object* v_whnfType_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_203_; uint8_t v_whnfType_boxed_204_; lean_object* v_res_205_; 
v_cleanupAnnotations_boxed_203_ = lean_unbox(v_cleanupAnnotations_196_);
v_whnfType_boxed_204_ = lean_unbox(v_whnfType_197_);
v_res_205_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(v_00_u03b1_192_, v_type_193_, v_maxFVars_x3f_194_, v_k_195_, v_cleanupAnnotations_boxed_203_, v_whnfType_boxed_204_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(lean_object* v_e_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = l_Lean_Expr_hasMVar(v_e_206_);
v___x_210_ = lean_bool_not(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v_mctx_212_; lean_object* v___x_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; lean_object* v_cache_217_; lean_object* v_zetaDeltaFVarIds_218_; lean_object* v_postponed_219_; lean_object* v_diag_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_229_; 
v___x_211_ = lean_st_ref_get(v___y_207_);
v_mctx_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_211_);
v___x_213_ = l_Lean_instantiateMVarsCore(v_mctx_212_, v_e_206_);
v_fst_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_fst_214_);
v_snd_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v___x_213_);
v___x_216_ = lean_st_ref_take(v___y_207_);
v_cache_217_ = lean_ctor_get(v___x_216_, 1);
v_zetaDeltaFVarIds_218_ = lean_ctor_get(v___x_216_, 2);
v_postponed_219_ = lean_ctor_get(v___x_216_, 3);
v_diag_220_ = lean_ctor_get(v___x_216_, 4);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_216_, 0);
lean_dec(v_unused_230_);
v___x_222_ = v___x_216_;
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_diag_220_);
lean_inc(v_postponed_219_);
lean_inc(v_zetaDeltaFVarIds_218_);
lean_inc(v_cache_217_);
lean_dec(v___x_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_snd_215_);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_snd_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_zetaDeltaFVarIds_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_postponed_219_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_diag_220_);
v___x_225_ = v_reuseFailAlloc_228_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_st_ref_set(v___y_207_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v_fst_214_);
return v___x_227_;
}
}
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_e_206_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg___boxed(lean_object* v_e_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_232_, v___y_233_);
lean_dec(v___y_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(lean_object* v_e_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_236_, v___y_238_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___boxed(lean_object* v_e_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(v_e_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(lean_object* v_as_251_, size_t v_sz_252_, size_t v_i_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_a_261_; uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_253_, v_sz_252_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_254_);
return v___x_266_;
}
else
{
lean_object* v_snd_267_; lean_object* v_fst_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_336_; 
v_snd_267_ = lean_ctor_get(v_b_254_, 1);
v_fst_268_ = lean_ctor_get(v_b_254_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_b_254_);
if (v_isSharedCheck_336_ == 0)
{
v___x_270_ = v_b_254_;
v_isShared_271_ = v_isSharedCheck_336_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_snd_267_);
lean_inc(v_fst_268_);
lean_dec(v_b_254_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_336_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_array_272_; lean_object* v_start_273_; lean_object* v_stop_274_; uint8_t v___x_275_; 
v_array_272_ = lean_ctor_get(v_snd_267_, 0);
v_start_273_ = lean_ctor_get(v_snd_267_, 1);
v_stop_274_ = lean_ctor_get(v_snd_267_, 2);
v___x_275_ = lean_nat_dec_lt(v_start_273_, v_stop_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_277_; 
if (v_isShared_271_ == 0)
{
v___x_277_ = v___x_270_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_fst_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_snd_267_);
v___x_277_ = v_reuseFailAlloc_279_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
else
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_332_; 
lean_inc(v_stop_274_);
lean_inc(v_start_273_);
lean_inc_ref(v_array_272_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_snd_267_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_333_ = lean_ctor_get(v_snd_267_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_snd_267_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_snd_267_, 0);
lean_dec(v_unused_335_);
v___x_281_ = v_snd_267_;
v_isShared_282_ = v_isSharedCheck_332_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_snd_267_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_332_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_array_uget_borrowed(v_as_251_, v_i_253_);
lean_inc(v_a_283_);
v___x_284_ = l_Lean_Meta_isProof(v_a_283_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = lean_array_fget(v_array_272_, v_start_273_);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_start_273_, v___x_287_);
lean_dec(v_start_273_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_288_);
v___x_290_ = v___x_281_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_array_272_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_stop_274_);
v___x_290_ = v_reuseFailAlloc_323_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
uint8_t v___x_291_; 
v___x_291_ = lean_unbox(v_a_285_);
lean_dec(v_a_285_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = l_Lean_Expr_fvarId_x21(v_a_283_);
v___x_293_ = l_Lean_FVarId_getUserName___redArg(v___x_292_, v___y_255_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
lean_inc(v_a_283_);
v___x_295_ = l_Lean_Meta_mkEqHEq(v_a_283_, v___x_286_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0));
v___x_298_ = lean_name_append_after(v_a_294_, v___x_297_);
v___x_299_ = 0;
v___x_300_ = l_Lean_mkForall(v___x_298_, v___x_299_, v_a_296_, v_fst_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v___x_290_);
lean_ctor_set(v___x_270_, 0, v___x_300_);
v___x_302_ = v___x_270_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_290_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v_a_261_ = v___x_302_;
goto v___jp_260_;
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_a_294_);
lean_dec_ref(v___x_290_);
lean_del_object(v___x_270_);
lean_dec(v_fst_268_);
v_a_304_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_295_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_295_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v___x_290_);
lean_dec(v___x_286_);
lean_del_object(v___x_270_);
lean_dec(v_fst_268_);
v_a_312_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_293_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_293_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v___x_286_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v___x_290_);
v___x_321_ = v___x_270_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_fst_268_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_290_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v_a_261_ = v___x_321_;
goto v___jp_260_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_del_object(v___x_281_);
lean_dec(v_stop_274_);
lean_dec(v_start_273_);
lean_dec_ref(v_array_272_);
lean_del_object(v___x_270_);
lean_dec(v_fst_268_);
v_a_324_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_284_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_284_);
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
}
}
}
v___jp_260_:
{
size_t v___x_262_; size_t v___x_263_; 
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_253_, v___x_262_);
v_i_253_ = v___x_263_;
v_b_254_ = v_a_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___boxed(lean_object* v_as_337_, lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_b_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
size_t v_sz_boxed_346_; size_t v_i_boxed_347_; lean_object* v_res_348_; 
v_sz_boxed_346_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_347_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v_as_337_, v_sz_boxed_346_, v_i_boxed_347_, v_b_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec_ref(v_as_337_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(lean_object* v_name_349_, lean_object* v_us_350_, lean_object* v_xs1_351_, lean_object* v_x1_352_, lean_object* v_xs2_353_, lean_object* v_x2_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_ctorIdxApp1_363_; lean_object* v___x_364_; lean_object* v_ctorIdxApp2_365_; lean_object* v___x_366_; 
v___x_360_ = l_Lean_mkCtorIdxName(v_name_349_);
v___x_361_ = l_Lean_mkConst(v___x_360_, v_us_350_);
v___x_362_ = lean_array_push(v_xs1_351_, v_x1_352_);
lean_inc_ref(v___x_361_);
v_ctorIdxApp1_363_ = l_Lean_mkAppN(v___x_361_, v___x_362_);
v___x_364_ = lean_array_push(v_xs2_353_, v_x2_354_);
v_ctorIdxApp2_365_ = l_Lean_mkAppN(v___x_361_, v___x_364_);
v___x_366_ = l_Lean_Meta_mkEq(v_ctorIdxApp1_363_, v_ctorIdxApp2_365_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; size_t v_sz_374_; size_t v___x_375_; lean_object* v___x_376_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
lean_inc_ref(v___x_364_);
v___x_368_ = l_Array_reverse___redArg(v___x_364_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_array_get_size(v___x_368_);
v___x_371_ = l_Array_toSubarray___redArg(v___x_368_, v___x_369_, v___x_370_);
lean_inc_ref(v___x_362_);
v___x_372_ = l_Array_reverse___redArg(v___x_362_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_a_367_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
v_sz_374_ = lean_array_size(v___x_372_);
v___x_375_ = ((size_t)0ULL);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v___x_372_, v_sz_374_, v___x_375_, v___x_373_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec_ref(v___x_372_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_fst_378_; lean_object* v___x_379_; uint8_t v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v_fst_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_fst_378_);
lean_dec(v_a_377_);
v___x_379_ = l_Array_append___redArg(v___x_362_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_380_ = 0;
v___x_381_ = 1;
v___x_382_ = 1;
v___x_383_ = l_Lean_Meta_mkForallFVars(v___x_379_, v_fst_378_, v___x_380_, v___x_381_, v___x_381_, v___x_382_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec_ref(v___x_379_);
return v___x_383_;
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_362_);
v_a_384_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_376_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_376_);
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
else
{
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_362_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed(lean_object* v_name_392_, lean_object* v_us_393_, lean_object* v_xs1_394_, lean_object* v_x1_395_, lean_object* v_xs2_396_, lean_object* v_x2_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(v_name_392_, v_us_393_, v_xs1_394_, v_x1_395_, v_xs2_396_, v_x2_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(lean_object* v_k_404_, lean_object* v_b_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_411_ = lean_apply_6(v_k_404_, v_b_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, lean_box(0));
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_k_412_, lean_object* v_b_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(v_k_412_, v_b_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(lean_object* v_name_420_, uint8_t v_bi_421_, lean_object* v_type_422_, lean_object* v_k_423_, uint8_t v_kind_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; 
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_430_, 0, v_k_423_);
v___x_431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_420_, v_bi_421_, v_type_422_, v___f_430_, v_kind_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
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
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_431_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_431_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_name_448_, lean_object* v_bi_449_, lean_object* v_type_450_, lean_object* v_k_451_, lean_object* v_kind_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_bi_boxed_458_; uint8_t v_kind_boxed_459_; lean_object* v_res_460_; 
v_bi_boxed_458_ = lean_unbox(v_bi_449_);
v_kind_boxed_459_ = lean_unbox(v_kind_452_);
v_res_460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_448_, v_bi_boxed_458_, v_type_450_, v_k_451_, v_kind_boxed_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(lean_object* v_name_461_, lean_object* v_type_462_, lean_object* v_k_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = 0;
v___x_470_ = 0;
v___x_471_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_461_, v___x_469_, v_type_462_, v_k_463_, v___x_470_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg___boxed(lean_object* v_name_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_472_, v_type_473_, v_k_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(lean_object* v_name_484_, lean_object* v_us_485_, lean_object* v_xs1_486_, lean_object* v_xs2_487_, lean_object* v___x_488_, lean_object* v_x1_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc_ref(v_xs2_487_);
v___f_495_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_495_, 0, v_name_484_);
lean_closure_set(v___f_495_, 1, v_us_485_);
lean_closure_set(v___f_495_, 2, v_xs1_486_);
lean_closure_set(v___f_495_, 3, v_x1_489_);
lean_closure_set(v___f_495_, 4, v_xs2_487_);
v___x_496_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1));
v___x_497_ = l_Lean_mkAppN(v___x_488_, v_xs2_487_);
lean_dec_ref(v_xs2_487_);
v___x_498_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v___x_496_, v___x_497_, v___f_495_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed(lean_object* v_name_499_, lean_object* v_us_500_, lean_object* v_xs1_501_, lean_object* v_xs2_502_, lean_object* v___x_503_, lean_object* v_x1_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(v_name_499_, v_us_500_, v_xs1_501_, v_xs2_502_, v___x_503_, v_x1_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(lean_object* v_00_u03b1_511_, lean_object* v_name_512_, lean_object* v_type_513_, lean_object* v_k_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_512_, v_type_513_, v_k_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed(lean_object* v_00_u03b1_521_, lean_object* v_name_522_, lean_object* v_type_523_, lean_object* v_k_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(v_00_u03b1_521_, v_name_522_, v_type_523_, v_k_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(lean_object* v_bs_531_, lean_object* v_k_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_531_, v_k_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg___boxed(lean_object* v_bs_555_, lean_object* v_k_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_555_, v_k_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v_bs_555_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(size_t v_sz_563_, size_t v_i_564_, lean_object* v_bs_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_566_ == 0)
{
return v_bs_565_;
}
else
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v_v_567_ = lean_array_uget(v_bs_565_, v_i_564_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_565_, v_i_564_, v___x_568_);
v___x_570_ = l_Lean_Expr_fvarId_x21(v_v_567_);
lean_dec(v_v_567_);
v___x_571_ = 1;
v___x_572_ = lean_box(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_564_, v___x_574_);
v___x_576_ = lean_array_uset(v_bs_x27_569_, v_i_564_, v___x_573_);
v_i_564_ = v___x_575_;
v_bs_565_ = v___x_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5___boxed(lean_object* v_sz_578_, lean_object* v_i_579_, lean_object* v_bs_580_){
_start:
{
size_t v_sz_boxed_581_; size_t v_i_boxed_582_; lean_object* v_res_583_; 
v_sz_boxed_581_ = lean_unbox_usize(v_sz_578_);
lean_dec(v_sz_578_);
v_i_boxed_582_ = lean_unbox_usize(v_i_579_);
lean_dec(v_i_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_boxed_581_, v_i_boxed_582_, v_bs_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(lean_object* v_bs_584_, lean_object* v_k_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
size_t v_sz_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_sz_591_ = lean_array_size(v_bs_584_);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_591_, v___x_592_, v_bs_584_);
v___x_594_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v___x_593_, v_k_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec_ref(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg___boxed(lean_object* v_bs_595_, lean_object* v_k_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_595_, v_k_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(lean_object* v_00_u03b1_603_, lean_object* v_bs_604_, lean_object* v_k_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_604_, v_k_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed(lean_object* v_00_u03b1_612_, lean_object* v_bs_613_, lean_object* v_k_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(v_00_u03b1_612_, v_bs_613_, v_k_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(lean_object* v_name_624_, lean_object* v_us_625_, lean_object* v_xs1_626_, lean_object* v_xs2_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1));
lean_inc(v_us_625_);
lean_inc(v_name_624_);
v___x_635_ = l_Lean_mkConst(v_name_624_, v_us_625_);
lean_inc_ref(v___x_635_);
lean_inc_ref_n(v_xs2_627_, 2);
lean_inc_ref(v_xs1_626_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed), 11, 5);
lean_closure_set(v___f_636_, 0, v_name_624_);
lean_closure_set(v___f_636_, 1, v_us_625_);
lean_closure_set(v___f_636_, 2, v_xs1_626_);
lean_closure_set(v___f_636_, 3, v_xs2_627_);
lean_closure_set(v___f_636_, 4, v___x_635_);
v___x_637_ = l_Lean_mkAppN(v___x_635_, v_xs1_626_);
v___x_638_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed), 9, 4);
lean_closure_set(v___x_638_, 0, lean_box(0));
lean_closure_set(v___x_638_, 1, v___x_634_);
lean_closure_set(v___x_638_, 2, v___x_637_);
lean_closure_set(v___x_638_, 3, v___f_636_);
v___x_639_ = lean_alloc_closure((void*)(l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed), 8, 3);
lean_closure_set(v___x_639_, 0, lean_box(0));
lean_closure_set(v___x_639_, 1, v_xs2_627_);
lean_closure_set(v___x_639_, 2, v___x_638_);
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed), 8, 3);
lean_closure_set(v___x_640_, 0, lean_box(0));
lean_closure_set(v___x_640_, 1, v_xs2_627_);
lean_closure_set(v___x_640_, 2, v___x_639_);
v___x_641_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_xs1_626_, v___x_640_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed(lean_object* v_name_642_, lean_object* v_us_643_, lean_object* v_xs1_644_, lean_object* v_xs2_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(v_name_642_, v_us_643_, v_xs1_644_, v_xs2_645_, v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v_x_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(lean_object* v_name_653_, lean_object* v_us_654_, lean_object* v_type_655_, lean_object* v___x_656_, lean_object* v_xs1_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___f_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v___f_664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed), 10, 3);
lean_closure_set(v___f_664_, 0, v_name_653_);
lean_closure_set(v___f_664_, 1, v_us_654_);
lean_closure_set(v___f_664_, 2, v_xs1_657_);
v___x_665_ = 0;
v___x_666_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_655_, v___x_656_, v___f_664_, v___x_665_, v___x_665_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed(lean_object* v_name_667_, lean_object* v_us_668_, lean_object* v_type_669_, lean_object* v___x_670_, lean_object* v_xs1_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(v_name_667_, v_us_668_, v_type_669_, v___x_670_, v_xs1_671_, v_x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v_x_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
if (lean_obj_tag(v_a_679_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_List_reverse___redArg(v_a_680_);
return v___x_681_;
}
else
{
lean_object* v_head_682_; lean_object* v_tail_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_692_; 
v_head_682_ = lean_ctor_get(v_a_679_, 0);
v_tail_683_ = lean_ctor_get(v_a_679_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_679_);
if (v_isSharedCheck_692_ == 0)
{
v___x_685_ = v_a_679_;
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_tail_683_);
lean_inc(v_head_682_);
lean_dec(v_a_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_mkLevelParam(v_head_682_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_a_680_);
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_a_680_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_679_ = v_tail_683_;
v_a_680_ = v___x_689_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_693_, lean_object* v_indVal_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_toConstantVal_700_; lean_object* v_numParams_701_; lean_object* v_numIndices_702_; lean_object* v_name_703_; lean_object* v_levelParams_704_; lean_object* v_type_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_782_; 
v_toConstantVal_700_ = lean_ctor_get(v_indVal_694_, 0);
lean_inc_ref(v_toConstantVal_700_);
v_numParams_701_ = lean_ctor_get(v_indVal_694_, 1);
lean_inc(v_numParams_701_);
v_numIndices_702_ = lean_ctor_get(v_indVal_694_, 2);
lean_inc(v_numIndices_702_);
lean_dec_ref(v_indVal_694_);
v_name_703_ = lean_ctor_get(v_toConstantVal_700_, 0);
v_levelParams_704_ = lean_ctor_get(v_toConstantVal_700_, 1);
v_type_705_ = lean_ctor_get(v_toConstantVal_700_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_toConstantVal_700_);
if (v_isSharedCheck_782_ == 0)
{
v___x_707_ = v_toConstantVal_700_;
v_isShared_708_ = v_isSharedCheck_782_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_type_705_);
lean_inc(v_levelParams_704_);
lean_inc(v_name_703_);
lean_dec(v_toConstantVal_700_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_782_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v_us_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; uint8_t v___x_714_; lean_object* v___x_715_; 
v___x_709_ = lean_box(0);
lean_inc(v_levelParams_704_);
v_us_710_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(v_levelParams_704_, v___x_709_);
v___x_711_ = lean_nat_add(v_numParams_701_, v_numIndices_702_);
lean_dec(v_numIndices_702_);
lean_dec(v_numParams_701_);
lean_inc(v___x_711_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_inc_ref(v___x_712_);
lean_inc_ref(v_type_705_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed), 11, 4);
lean_closure_set(v___f_713_, 0, v_name_703_);
lean_closure_set(v___f_713_, 1, v_us_710_);
lean_closure_set(v___f_713_, 2, v_type_705_);
lean_closure_set(v___f_713_, 3, v___x_712_);
v___x_714_ = 0;
v___x_715_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_705_, v___x_712_, v___f_713_, v___x_714_, v___x_714_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = lean_box(0);
v___x_718_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_716_, v___x_717_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_Expr_mvarId_x21(v_a_719_);
v___x_721_ = lean_unsigned_to_nat(2u);
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_add(v___x_711_, v___x_722_);
lean_dec(v___x_711_);
v___x_724_ = lean_nat_mul(v___x_721_, v___x_723_);
lean_dec(v___x_723_);
v___x_725_ = l_Lean_Meta_introNCore(v___x_720_, v___x_724_, v___x_709_, v___x_714_, v___x_714_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_756_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v_snd_727_ = lean_ctor_get(v_a_726_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_a_726_, 0);
lean_dec(v_unused_757_);
v___x_729_ = v_a_726_;
v_isShared_730_ = v_isSharedCheck_756_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_dec(v_a_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_756_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_snd_727_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref_known(v___x_731_, 1);
v___x_732_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_a_719_, v_a_696_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_747_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
lean_inc(v_thmName_693_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 2, v_a_716_);
lean_ctor_set(v___x_707_, 0, v_thmName_693_);
v___x_738_ = v___x_707_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_thmName_693_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_levelParams_704_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_a_716_);
v___x_738_ = v_reuseFailAlloc_746_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 1, v___x_709_);
lean_ctor_set(v___x_729_, 0, v_thmName_693_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_thmName_693_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_709_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v_a_733_);
lean_ctor_set(v___x_741_, 2, v___x_740_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_741_);
v___x_743_ = v___x_735_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
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
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_del_object(v___x_729_);
lean_dec(v_a_719_);
lean_dec(v_a_716_);
lean_del_object(v___x_707_);
lean_dec(v_levelParams_704_);
lean_dec(v_thmName_693_);
v_a_748_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_731_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_731_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_719_);
lean_dec(v_a_716_);
lean_del_object(v___x_707_);
lean_dec(v_levelParams_704_);
lean_dec(v_thmName_693_);
v_a_758_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_725_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_725_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_716_);
lean_dec(v___x_711_);
lean_del_object(v___x_707_);
lean_dec(v_levelParams_704_);
lean_dec(v_thmName_693_);
v_a_766_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_718_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_718_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v___x_711_);
lean_del_object(v___x_707_);
lean_dec(v_levelParams_704_);
lean_dec(v_thmName_693_);
v_a_774_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_715_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_715_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_783_, lean_object* v_indVal_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_783_, v_indVal_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(lean_object* v_00_u03b1_791_, lean_object* v_name_792_, uint8_t v_bi_793_, lean_object* v_type_794_, lean_object* v_k_795_, uint8_t v_kind_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_792_, v_bi_793_, v_type_794_, v_k_795_, v_kind_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b1_803_, lean_object* v_name_804_, lean_object* v_bi_805_, lean_object* v_type_806_, lean_object* v_k_807_, lean_object* v_kind_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v_bi_boxed_814_; uint8_t v_kind_boxed_815_; lean_object* v_res_816_; 
v_bi_boxed_814_ = lean_unbox(v_bi_805_);
v_kind_boxed_815_ = lean_unbox(v_kind_808_);
v_res_816_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(v_00_u03b1_803_, v_name_804_, v_bi_boxed_814_, v_type_806_, v_k_807_, v_kind_boxed_815_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(lean_object* v_00_u03b1_817_, lean_object* v_bs_818_, lean_object* v_k_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_818_, v_k_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___boxed(lean_object* v_00_u03b1_826_, lean_object* v_bs_827_, lean_object* v_k_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(v_00_u03b1_826_, v_bs_827_, v_k_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_bs_827_);
return v_res_834_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(lean_object* v_env_835_, lean_object* v_n_836_){
_start:
{
if (lean_obj_tag(v_n_836_) == 1)
{
lean_object* v_pre_837_; lean_object* v_str_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_pre_837_ = lean_ctor_get(v_n_836_, 0);
lean_inc(v_pre_837_);
v_str_838_ = lean_ctor_get(v_n_836_, 1);
lean_inc_ref(v_str_838_);
lean_dec_ref_known(v_n_836_, 2);
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0));
v___x_840_ = lean_string_dec_eq(v_str_838_, v___x_839_);
lean_dec_ref(v_str_838_);
if (v___x_840_ == 0)
{
lean_dec(v_pre_837_);
lean_dec_ref(v_env_835_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_isCtorIdxCore_x3f(v_env_835_, v_pre_837_);
if (lean_obj_tag(v___x_841_) == 0)
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
else
{
lean_dec_ref_known(v___x_841_, 1);
return v___x_840_;
}
}
}
else
{
uint8_t v___x_843_; 
lean_dec(v_n_836_);
lean_dec_ref(v_env_835_);
v___x_843_ = 0;
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object* v_env_844_, lean_object* v_n_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(v_env_844_, v_n_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_850_; lean_object* v___x_851_; 
v___f_850_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_));
v___x_851_ = l_Lean_registerReservedNamePredicate(v___f_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_env_858_; lean_object* v_toConstantVal_859_; lean_object* v_value_860_; lean_object* v_all_861_; uint8_t v___y_863_; lean_object* v_type_871_; uint8_t v___x_872_; 
v___x_857_ = lean_st_ref_get(v___y_855_);
v_env_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc_ref_n(v_env_858_, 2);
lean_dec(v___x_857_);
v_toConstantVal_859_ = lean_ctor_get(v_thm_854_, 0);
v_value_860_ = lean_ctor_get(v_thm_854_, 1);
v_all_861_ = lean_ctor_get(v_thm_854_, 2);
v_type_871_ = lean_ctor_get(v_toConstantVal_859_, 2);
v___x_872_ = l_Lean_Environment_hasUnsafe(v_env_858_, v_type_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Environment_hasUnsafe(v_env_858_, v_value_860_);
v___y_863_ = v___x_873_;
goto v___jp_862_;
}
else
{
lean_dec_ref(v_env_858_);
v___y_863_ = v___x_872_;
goto v___jp_862_;
}
v___jp_862_:
{
if (v___y_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_864_, 0, v_thm_854_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_inc(v_all_861_);
lean_inc_ref(v_value_860_);
lean_inc_ref(v_toConstantVal_859_);
lean_dec_ref(v_thm_854_);
v___x_866_ = lean_box(0);
v___x_867_ = 0;
v___x_868_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_868_, 0, v_toConstantVal_859_);
lean_ctor_set(v___x_868_, 1, v_value_860_);
lean_ctor_set(v___x_868_, 2, v___x_866_);
lean_ctor_set(v___x_868_, 3, v_all_861_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*4, v___x_867_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_874_, v___y_875_);
lean_dec(v___y_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(lean_object* v_thm_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_878_, v___y_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(v_thm_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object* v_name_892_, lean_object* v_val_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_892_, v_val_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v_a_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_a_900_, v___y_897_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_901_);
v___x_903_ = 0;
v___x_904_ = l_Lean_addDecl(v_a_902_, v___x_903_, v___y_896_, v___y_897_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_899_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_899_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v_name_913_, lean_object* v_val_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v_name_913_, v_val_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_920_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_unsigned_to_nat(32u);
v___x_925_ = lean_mk_empty_array_with_capacity(v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
size_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_927_ = ((size_t)5ULL);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_unsigned_to_nat(32u);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_932_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
lean_ctor_set(v___x_932_, 2, v___x_928_);
lean_ctor_set(v___x_932_, 3, v___x_928_);
lean_ctor_set_usize(v___x_932_, 4, v___x_927_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_933_ = lean_box(1);
v___x_934_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
lean_ctor_set(v___x_936_, 2, v___x_933_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
lean_ctor_set(v___x_941_, 3, v___x_940_);
lean_ctor_set(v___x_941_, 4, v___x_939_);
lean_ctor_set(v___x_941_, 5, v___x_939_);
lean_ctor_set(v___x_941_, 6, v___x_939_);
lean_ctor_set(v___x_941_, 7, v___x_939_);
lean_ctor_set(v___x_941_, 8, v___x_939_);
lean_ctor_set(v___x_941_, 9, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_943_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
lean_ctor_set(v___x_943_, 3, v___x_942_);
lean_ctor_set(v___x_943_, 4, v___x_942_);
lean_ctor_set(v___x_943_, 5, v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
lean_ctor_set(v___x_945_, 4, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object* v___x_946_, lean_object* v_name_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
if (lean_obj_tag(v_name_947_) == 1)
{
lean_object* v_pre_955_; lean_object* v_str_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_pre_955_ = lean_ctor_get(v_name_947_, 0);
lean_inc(v_pre_955_);
v_str_956_ = lean_ctor_get(v_name_947_, 1);
v___x_957_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0));
v___x_958_ = lean_string_dec_eq(v_str_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_pre_955_);
lean_dec_ref_known(v_name_947_, 2);
lean_dec(v___x_946_);
goto v___jp_951_;
}
else
{
lean_object* v___x_959_; lean_object* v_env_960_; lean_object* v___x_961_; 
v___x_959_ = lean_st_ref_get(v___y_949_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
lean_inc(v_pre_955_);
v___x_961_ = l_Lean_isCtorIdxCore_x3f(v_env_960_, v_pre_955_);
if (lean_obj_tag(v___x_961_) == 1)
{
lean_object* v_val_962_; uint8_t v___x_963_; uint8_t v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; uint64_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = 0;
v___x_964_ = 1;
v___x_965_ = 0;
v___x_966_ = 2;
v___x_967_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_967_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 1, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 2, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 3, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 4, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 5, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 6, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 7, v___x_963_);
lean_ctor_set_uint8(v___x_967_, 8, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 9, v___x_964_);
lean_ctor_set_uint8(v___x_967_, 10, v___x_965_);
lean_ctor_set_uint8(v___x_967_, 11, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 12, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 13, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 14, v___x_966_);
lean_ctor_set_uint8(v___x_967_, 15, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 16, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 17, v___x_958_);
lean_ctor_set_uint8(v___x_967_, 18, v___x_958_);
v___x_968_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set_uint64(v___x_969_, sizeof(void*)*1, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_));
v___x_974_ = lean_box(0);
lean_inc(v___x_946_);
v___x_975_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_975_, 0, v___x_969_);
lean_ctor_set(v___x_975_, 1, v___x_946_);
lean_ctor_set(v___x_975_, 2, v___x_972_);
lean_ctor_set(v___x_975_, 3, v___x_973_);
lean_ctor_set(v___x_975_, 4, v___x_974_);
lean_ctor_set(v___x_975_, 5, v___x_970_);
lean_ctor_set(v___x_975_, 6, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*7, v___x_963_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*7 + 1, v___x_963_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*7 + 2, v___x_963_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*7 + 3, v___x_958_);
v___x_976_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_978_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_979_, 0, v___x_976_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
lean_ctor_set(v___x_979_, 2, v___x_946_);
lean_ctor_set(v___x_979_, 3, v___x_971_);
lean_ctor_set(v___x_979_, 4, v___x_978_);
v___x_980_ = lean_st_mk_ref(v___x_979_);
lean_inc_ref(v_name_947_);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_981_, 0, v_name_947_);
lean_closure_set(v___f_981_, 1, v_val_962_);
v___x_982_ = l_Lean_Meta_realizeConst(v_pre_955_, v_name_947_, v___f_981_, v___x_975_, v___x_980_, v___y_948_, v___y_949_);
lean_dec_ref_known(v___x_975_, 7);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_991_; 
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_982_, 0);
lean_dec(v_unused_992_);
v___x_984_ = v___x_982_;
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
else
{
lean_dec(v___x_982_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_986_ = lean_st_ref_get(v___x_980_);
lean_dec(v___x_980_);
lean_dec(v___x_986_);
v___x_987_ = lean_box(v___x_958_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___x_980_);
v_a_993_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_982_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_982_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v___x_961_);
lean_dec(v_pre_955_);
lean_dec_ref_known(v_name_947_, 2);
lean_dec(v___x_946_);
v___x_1001_ = 0;
v___x_1002_ = lean_box(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
else
{
lean_dec(v_name_947_);
lean_dec(v___x_946_);
goto v___jp_951_;
}
v___jp_951_:
{
uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = 0;
v___x_953_ = lean_box(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v___x_1004_, lean_object* v_name_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v___x_1004_, v_name_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_));
v___x_1014_ = l_Lean_registerReservedNameAction(v___f_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
return v_res_1016_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CtorIdxHInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CtorIdxHInj(builtin);
}
#ifdef __cplusplus
}
#endif
