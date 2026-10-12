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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(lean_object* v_mvarId_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
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
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_7_ = stack[0].m_obj;
lean_object* v_a_8_ = stack[1].m_obj;
lean_object* v_a_9_ = stack[2].m_obj;
lean_object* v_a_10_ = stack[3].m_obj;
lean_object* v_a_11_ = stack[4].m_obj;
lean_object* v_res_64_;
v_res_64_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_mvarId_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl___boxed(lean_object* v_mvarId_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_mvarId_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_71_;
}
}
lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(lean_object* v_xs_72_, lean_object* v_k_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(lean_box(0), v_xs_72_, v_k_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_79_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_79_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_72_ = stack[0].m_obj;
lean_object* v_k_73_ = stack[1].m_obj;
lean_object* v___y_74_ = stack[2].m_obj;
lean_object* v___y_75_ = stack[3].m_obj;
lean_object* v___y_76_ = stack[4].m_obj;
lean_object* v___y_77_ = stack[5].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_72_, v_k_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg___boxed(lean_object* v_xs_97_, lean_object* v_k_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_97_, v_k_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(lean_object* v_00_u03b1_105_, lean_object* v_xs_106_, lean_object* v_k_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_106_, v_k_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_106_ = stack[1].m_obj;
lean_object* v_k_107_ = stack[2].m_obj;
lean_object* v___y_108_ = stack[3].m_obj;
lean_object* v___y_109_ = stack[4].m_obj;
lean_object* v___y_110_ = stack[5].m_obj;
lean_object* v___y_111_ = stack[6].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(lean_box(0), v_xs_106_, v_k_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed(lean_object* v_00_u03b1_115_, lean_object* v_xs_116_, lean_object* v_k_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(v_00_u03b1_115_, v_xs_116_, v_k_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(lean_object* v_k_124_, lean_object* v_b_125_, lean_object* v_c_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
v___x_132_ = lean_apply_7(v_k_124_, v_b_125_, v_c_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_124_ = stack[0].m_obj;
lean_object* v_b_125_ = stack[1].m_obj;
lean_object* v_c_126_ = stack[2].m_obj;
lean_object* v___y_127_ = stack[3].m_obj;
lean_object* v___y_128_ = stack[4].m_obj;
lean_object* v___y_129_ = stack[5].m_obj;
lean_object* v___y_130_ = stack[6].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(v_k_124_, v_b_125_, v_c_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed(lean_object* v_k_134_, lean_object* v_b_135_, lean_object* v_c_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(v_k_134_, v_b_135_, v_c_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_142_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(lean_object* v_type_143_, lean_object* v_maxFVars_x3f_144_, lean_object* v_k_145_, uint8_t v_cleanupAnnotations_146_, uint8_t v_whnfType_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; 
v___f_153_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_153_, 0, v_k_145_);
v___x_154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_143_, v_maxFVars_x3f_144_, v___f_153_, v_cleanupAnnotations_146_, v_whnfType_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_a_163_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_154_);
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
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_143_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_144_ = stack[1].m_obj;
lean_object* v_k_145_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_146_ = stack[3].m_num;
uint8_t v_whnfType_147_ = stack[4].m_num;
lean_object* v___y_148_ = stack[5].m_obj;
lean_object* v___y_149_ = stack[6].m_obj;
lean_object* v___y_150_ = stack[7].m_obj;
lean_object* v___y_151_ = stack[8].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_143_, v_maxFVars_x3f_144_, v_k_145_, v_cleanupAnnotations_146_, v_whnfType_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___boxed(lean_object* v_type_172_, lean_object* v_maxFVars_x3f_173_, lean_object* v_k_174_, lean_object* v_cleanupAnnotations_175_, lean_object* v_whnfType_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_182_; uint8_t v_whnfType_boxed_183_; lean_object* v_res_184_; 
v_cleanupAnnotations_boxed_182_ = lean_unbox(v_cleanupAnnotations_175_);
v_whnfType_boxed_183_ = lean_unbox(v_whnfType_176_);
v_res_184_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_172_, v_maxFVars_x3f_173_, v_k_174_, v_cleanupAnnotations_boxed_182_, v_whnfType_boxed_183_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_184_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(lean_object* v_00_u03b1_185_, lean_object* v_type_186_, lean_object* v_maxFVars_x3f_187_, lean_object* v_k_188_, uint8_t v_cleanupAnnotations_189_, uint8_t v_whnfType_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_186_, v_maxFVars_x3f_187_, v_k_188_, v_cleanupAnnotations_189_, v_whnfType_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_186_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_187_ = stack[2].m_obj;
lean_object* v_k_188_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_189_ = stack[4].m_num;
uint8_t v_whnfType_190_ = stack[5].m_num;
lean_object* v___y_191_ = stack[6].m_obj;
lean_object* v___y_192_ = stack[7].m_obj;
lean_object* v___y_193_ = stack[8].m_obj;
lean_object* v___y_194_ = stack[9].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(lean_box(0), v_type_186_, v_maxFVars_x3f_187_, v_k_188_, v_cleanupAnnotations_189_, v_whnfType_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___boxed(lean_object* v_00_u03b1_198_, lean_object* v_type_199_, lean_object* v_maxFVars_x3f_200_, lean_object* v_k_201_, lean_object* v_cleanupAnnotations_202_, lean_object* v_whnfType_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_209_; uint8_t v_whnfType_boxed_210_; lean_object* v_res_211_; 
v_cleanupAnnotations_boxed_209_ = lean_unbox(v_cleanupAnnotations_202_);
v_whnfType_boxed_210_ = lean_unbox(v_whnfType_203_);
v_res_211_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(v_00_u03b1_198_, v_type_199_, v_maxFVars_x3f_200_, v_k_201_, v_cleanupAnnotations_boxed_209_, v_whnfType_boxed_210_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_211_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(lean_object* v_e_212_, lean_object* v___y_213_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Expr_hasMVar(v_e_212_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_e_212_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v_mctx_218_; lean_object* v___x_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v_cache_223_; lean_object* v_zetaDeltaFVarIds_224_; lean_object* v_postponed_225_; lean_object* v_diag_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_235_; 
v___x_217_ = lean_st_ref_get(v___y_213_);
v_mctx_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref(v_mctx_218_);
lean_dec(v___x_217_);
v___x_219_ = l_Lean_instantiateMVarsCore(v_mctx_218_, v_e_212_);
v_fst_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_fst_220_);
v_snd_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc(v_snd_221_);
lean_dec_ref(v___x_219_);
v___x_222_ = lean_st_ref_take(v___y_213_);
v_cache_223_ = lean_ctor_get(v___x_222_, 1);
v_zetaDeltaFVarIds_224_ = lean_ctor_get(v___x_222_, 2);
v_postponed_225_ = lean_ctor_get(v___x_222_, 3);
v_diag_226_ = lean_ctor_get(v___x_222_, 4);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v___x_222_, 0);
lean_dec(v_unused_236_);
v___x_228_ = v___x_222_;
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_diag_226_);
lean_inc(v_postponed_225_);
lean_inc(v_zetaDeltaFVarIds_224_);
lean_inc(v_cache_223_);
lean_dec(v___x_222_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v_snd_221_);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_snd_221_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_cache_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_zetaDeltaFVarIds_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_postponed_225_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_diag_226_);
v___x_231_ = v_reuseFailAlloc_234_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_st_ref_put(v___y_213_, v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_fst_220_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_212_ = stack[0].m_obj;
lean_object* v___y_213_ = stack[1].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_212_, v___y_213_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg___boxed(lean_object* v_e_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_238_, v___y_239_);
lean_dec(v___y_239_);
return v_res_241_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(lean_object* v_e_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_242_, v___y_244_);
return v___x_248_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_242_ = stack[0].m_obj;
lean_object* v___y_243_ = stack[1].m_obj;
lean_object* v___y_244_ = stack[2].m_obj;
lean_object* v___y_245_ = stack[3].m_obj;
lean_object* v___y_246_ = stack[4].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(v_e_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___boxed(lean_object* v_e_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(v_e_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(lean_object* v_as_258_, size_t v_sz_259_, size_t v_i_260_, lean_object* v_b_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_a_268_; uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_lt(v_i_260_, v_sz_259_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v_b_261_);
return v___x_273_;
}
else
{
lean_object* v_snd_274_; lean_object* v_fst_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_343_; 
v_snd_274_ = lean_ctor_get(v_b_261_, 1);
v_fst_275_ = lean_ctor_get(v_b_261_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_b_261_);
if (v_isSharedCheck_343_ == 0)
{
v___x_277_ = v_b_261_;
v_isShared_278_ = v_isSharedCheck_343_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_274_);
lean_inc(v_fst_275_);
lean_dec(v_b_261_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_343_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_array_279_; lean_object* v_start_280_; lean_object* v_stop_281_; uint8_t v___x_282_; 
v_array_279_ = lean_ctor_get(v_snd_274_, 0);
v_start_280_ = lean_ctor_get(v_snd_274_, 1);
v_stop_281_ = lean_ctor_get(v_snd_274_, 2);
v___x_282_ = lean_nat_dec_lt(v_start_280_, v_stop_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_284_; 
if (v_isShared_278_ == 0)
{
v___x_284_ = v___x_277_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_fst_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_274_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_339_; 
lean_inc(v_stop_281_);
lean_inc(v_start_280_);
lean_inc_ref(v_array_279_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_snd_274_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; lean_object* v_unused_341_; lean_object* v_unused_342_; 
v_unused_340_ = lean_ctor_get(v_snd_274_, 2);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_snd_274_, 1);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_snd_274_, 0);
lean_dec(v_unused_342_);
v___x_288_ = v_snd_274_;
v_isShared_289_ = v_isSharedCheck_339_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_snd_274_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_339_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_a_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v_a_290_ = lean_array_uget_borrowed(v_as_258_, v_i_260_);
v___x_291_ = lean_array_fget(v_array_279_, v_start_280_);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_start_280_, v___x_292_);
lean_dec(v_start_280_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_293_);
v___x_295_ = v___x_288_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_array_279_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_stop_281_);
v___x_295_ = v_reuseFailAlloc_338_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; 
lean_inc(v_a_290_);
v___x_296_ = l_Lean_Meta_isProof(v_a_290_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = lean_unbox(v_a_297_);
lean_dec(v_a_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_Expr_fvarId_x21(v_a_290_);
v___x_300_ = l_Lean_FVarId_getUserName___redArg(v___x_299_, v___y_262_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0));
v___x_303_ = lean_name_append_after(v_a_301_, v___x_302_);
lean_inc(v_a_290_);
v___x_304_ = l_Lean_Meta_mkEqHEq(v_a_290_, v___x_291_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = 0;
v___x_307_ = l_Lean_mkForall(v___x_303_, v___x_306_, v_a_305_, v_fst_275_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_295_);
lean_ctor_set(v___x_277_, 0, v___x_307_);
v___x_309_ = v___x_277_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_295_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
v_a_268_ = v___x_309_;
goto v___jp_267_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v___x_303_);
lean_dec_ref(v___x_295_);
lean_del_object(v___x_277_);
lean_dec(v_fst_275_);
v_a_311_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_304_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_304_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v___x_295_);
lean_dec(v___x_291_);
lean_del_object(v___x_277_);
lean_dec(v_fst_275_);
v_a_319_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_300_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_300_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v___x_291_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_295_);
v___x_328_ = v___x_277_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_275_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_295_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_268_ = v___x_328_;
goto v___jp_267_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___x_295_);
lean_dec(v___x_291_);
lean_del_object(v___x_277_);
lean_dec(v_fst_275_);
v_a_330_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_296_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_296_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
}
v___jp_267_:
{
size_t v___x_269_; size_t v___x_270_; 
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_i_260_, v___x_269_);
v_i_260_ = v___x_270_;
v_b_261_ = v_a_268_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_258_ = stack[0].m_obj;
size_t v_sz_259_ = stack[1].m_num;
size_t v_i_260_ = stack[2].m_num;
lean_object* v_b_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v___y_263_ = stack[5].m_obj;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v___y_265_ = stack[7].m_obj;
lean_object* v_res_344_;
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v_as_258_, v_sz_259_, v_i_260_, v_b_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___boxed(lean_object* v_as_345_, lean_object* v_sz_346_, lean_object* v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_346_);
lean_dec(v_sz_346_);
v_i_boxed_355_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v_as_345_, v_sz_boxed_354_, v_i_boxed_355_, v_b_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v_as_345_);
return v_res_356_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(lean_object* v_name_357_, lean_object* v_us_358_, lean_object* v_xs1_359_, lean_object* v_x1_360_, lean_object* v_xs2_361_, lean_object* v_x2_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_ctorIdxApp1_371_; lean_object* v___x_372_; lean_object* v_ctorIdxApp2_373_; lean_object* v___x_374_; 
v___x_368_ = l_Lean_mkCtorIdxName(v_name_357_);
v___x_369_ = l_Lean_mkConst(v___x_368_, v_us_358_);
v___x_370_ = lean_array_push(v_xs1_359_, v_x1_360_);
lean_inc_ref(v___x_369_);
v_ctorIdxApp1_371_ = l_Lean_mkAppN(v___x_369_, v___x_370_);
v___x_372_ = lean_array_push(v_xs2_361_, v_x2_362_);
v_ctorIdxApp2_373_ = l_Lean_mkAppN(v___x_369_, v___x_372_);
v___x_374_ = l_Lean_Meta_mkEq(v_ctorIdxApp1_371_, v_ctorIdxApp2_373_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; size_t v_sz_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
lean_inc_ref(v___x_372_);
v___x_376_ = l_Array_reverse___redArg(v___x_372_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_array_get_size(v___x_376_);
v___x_379_ = l_Array_toSubarray___redArg(v___x_376_, v___x_377_, v___x_378_);
lean_inc_ref(v___x_370_);
v___x_380_ = l_Array_reverse___redArg(v___x_370_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_a_375_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
v_sz_382_ = lean_array_size(v___x_380_);
v___x_383_ = ((size_t)0ULL);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v___x_380_, v_sz_382_, v___x_383_, v___x_381_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec_ref(v___x_380_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_fst_386_; lean_object* v___x_387_; uint8_t v___x_388_; uint8_t v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v_fst_386_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_fst_386_);
lean_dec(v_a_385_);
v___x_387_ = l_Array_append___redArg(v___x_370_, v___x_372_);
lean_dec_ref(v___x_372_);
v___x_388_ = 0;
v___x_389_ = 1;
v___x_390_ = 1;
v___x_391_ = l_Lean_Meta_mkForallFVars(v___x_387_, v_fst_386_, v___x_388_, v___x_389_, v___x_389_, v___x_390_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec_ref(v___x_387_);
return v___x_391_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_370_);
v_a_392_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_384_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_384_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_370_);
return v___x_374_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_357_ = stack[0].m_obj;
lean_object* v_us_358_ = stack[1].m_obj;
lean_object* v_xs1_359_ = stack[2].m_obj;
lean_object* v_x1_360_ = stack[3].m_obj;
lean_object* v_xs2_361_ = stack[4].m_obj;
lean_object* v_x2_362_ = stack[5].m_obj;
lean_object* v___y_363_ = stack[6].m_obj;
lean_object* v___y_364_ = stack[7].m_obj;
lean_object* v___y_365_ = stack[8].m_obj;
lean_object* v___y_366_ = stack[9].m_obj;
lean_object* v_res_400_;
v_res_400_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(v_name_357_, v_us_358_, v_xs1_359_, v_x1_360_, v_xs2_361_, v_x2_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed(lean_object* v_name_401_, lean_object* v_us_402_, lean_object* v_xs1_403_, lean_object* v_x1_404_, lean_object* v_xs2_405_, lean_object* v_x2_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(v_name_401_, v_us_402_, v_xs1_403_, v_x1_404_, v_xs2_405_, v_x2_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_412_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(lean_object* v_k_413_, lean_object* v_b_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
v___x_420_ = lean_apply_6(v_k_413_, v_b_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_413_ = stack[0].m_obj;
lean_object* v_b_414_ = stack[1].m_obj;
lean_object* v___y_415_ = stack[2].m_obj;
lean_object* v___y_416_ = stack[3].m_obj;
lean_object* v___y_417_ = stack[4].m_obj;
lean_object* v___y_418_ = stack[5].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(v_k_413_, v_b_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_k_422_, lean_object* v_b_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(v_k_422_, v_b_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(lean_object* v_name_430_, uint8_t v_bi_431_, lean_object* v_type_432_, lean_object* v_k_433_, uint8_t v_kind_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; 
v___f_440_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_440_, 0, v_k_433_);
v___x_441_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_430_, v_bi_431_, v_type_432_, v___f_440_, v_kind_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
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
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_441_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_430_ = stack[0].m_obj;
uint8_t v_bi_431_ = stack[1].m_num;
lean_object* v_type_432_ = stack[2].m_obj;
lean_object* v_k_433_ = stack[3].m_obj;
uint8_t v_kind_434_ = stack[4].m_num;
lean_object* v___y_435_ = stack[5].m_obj;
lean_object* v___y_436_ = stack[6].m_obj;
lean_object* v___y_437_ = stack[7].m_obj;
lean_object* v___y_438_ = stack[8].m_obj;
lean_object* v_res_458_;
v_res_458_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_430_, v_bi_431_, v_type_432_, v_k_433_, v_kind_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_name_459_, lean_object* v_bi_460_, lean_object* v_type_461_, lean_object* v_k_462_, lean_object* v_kind_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_bi_boxed_469_; uint8_t v_kind_boxed_470_; lean_object* v_res_471_; 
v_bi_boxed_469_ = lean_unbox(v_bi_460_);
v_kind_boxed_470_ = lean_unbox(v_kind_463_);
v_res_471_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_459_, v_bi_boxed_469_, v_type_461_, v_k_462_, v_kind_boxed_470_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_471_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(lean_object* v_name_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = 0;
v___x_481_ = 0;
v___x_482_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_472_, v___x_480_, v_type_473_, v_k_474_, v___x_481_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_472_ = stack[0].m_obj;
lean_object* v_type_473_ = stack[1].m_obj;
lean_object* v_k_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_472_, v_type_473_, v_k_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg___boxed(lean_object* v_name_484_, lean_object* v_type_485_, lean_object* v_k_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_484_, v_type_485_, v_k_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_492_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(lean_object* v_name_496_, lean_object* v_us_497_, lean_object* v_xs1_498_, lean_object* v_xs2_499_, lean_object* v___x_500_, lean_object* v_x1_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc_ref(v_xs2_499_);
v___f_507_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_507_, 0, v_name_496_);
lean_closure_set(v___f_507_, 1, v_us_497_);
lean_closure_set(v___f_507_, 2, v_xs1_498_);
lean_closure_set(v___f_507_, 3, v_x1_501_);
lean_closure_set(v___f_507_, 4, v_xs2_499_);
v___x_508_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1));
v___x_509_ = l_Lean_mkAppN(v___x_500_, v_xs2_499_);
lean_dec_ref(v_xs2_499_);
v___x_510_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v___x_508_, v___x_509_, v___f_507_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_510_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_496_ = stack[0].m_obj;
lean_object* v_us_497_ = stack[1].m_obj;
lean_object* v_xs1_498_ = stack[2].m_obj;
lean_object* v_xs2_499_ = stack[3].m_obj;
lean_object* v___x_500_ = stack[4].m_obj;
lean_object* v_x1_501_ = stack[5].m_obj;
lean_object* v___y_502_ = stack[6].m_obj;
lean_object* v___y_503_ = stack[7].m_obj;
lean_object* v___y_504_ = stack[8].m_obj;
lean_object* v___y_505_ = stack[9].m_obj;
lean_object* v_res_511_;
v_res_511_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(v_name_496_, v_us_497_, v_xs1_498_, v_xs2_499_, v___x_500_, v_x1_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed(lean_object* v_name_512_, lean_object* v_us_513_, lean_object* v_xs1_514_, lean_object* v_xs2_515_, lean_object* v___x_516_, lean_object* v_x1_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(v_name_512_, v_us_513_, v_xs1_514_, v_xs2_515_, v___x_516_, v_x1_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(lean_object* v_00_u03b1_524_, lean_object* v_name_525_, lean_object* v_type_526_, lean_object* v_k_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_525_, v_type_526_, v_k_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_525_ = stack[1].m_obj;
lean_object* v_type_526_ = stack[2].m_obj;
lean_object* v_k_527_ = stack[3].m_obj;
lean_object* v___y_528_ = stack[4].m_obj;
lean_object* v___y_529_ = stack[5].m_obj;
lean_object* v___y_530_ = stack[6].m_obj;
lean_object* v___y_531_ = stack[7].m_obj;
lean_object* v_res_534_;
v_res_534_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(lean_box(0), v_name_525_, v_type_526_, v_k_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed(lean_object* v_00_u03b1_535_, lean_object* v_name_536_, lean_object* v_type_537_, lean_object* v_k_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(v_00_u03b1_535_, v_name_536_, v_type_537_, v_k_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(lean_object* v_bs_545_, lean_object* v_k_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_545_, v_k_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_552_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_552_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_545_ = stack[0].m_obj;
lean_object* v_k_546_ = stack[1].m_obj;
lean_object* v___y_547_ = stack[2].m_obj;
lean_object* v___y_548_ = stack[3].m_obj;
lean_object* v___y_549_ = stack[4].m_obj;
lean_object* v___y_550_ = stack[5].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_545_, v_k_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg___boxed(lean_object* v_bs_570_, lean_object* v_k_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_570_, v_k_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v_bs_570_);
return v_res_577_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(size_t v_sz_578_, size_t v_i_579_, lean_object* v_bs_580_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_581_ == 0)
{
return v_bs_580_;
}
else
{
lean_object* v_v_582_; lean_object* v___x_583_; lean_object* v_bs_x27_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v_v_582_ = lean_array_uget(v_bs_580_, v_i_579_);
v___x_583_ = lean_unsigned_to_nat(0u);
v_bs_x27_584_ = lean_array_uset(v_bs_580_, v_i_579_, v___x_583_);
v___x_585_ = l_Lean_Expr_fvarId_x21(v_v_582_);
lean_dec(v_v_582_);
v___x_586_ = 1;
v___x_587_ = lean_box(v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_585_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_579_, v___x_589_);
v___x_591_ = lean_array_uset(v_bs_x27_584_, v_i_579_, v___x_588_);
v_i_579_ = v___x_590_;
v_bs_580_ = v___x_591_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_578_ = stack[0].m_num;
size_t v_i_579_ = stack[1].m_num;
lean_object* v_bs_580_ = stack[2].m_obj;
lean_object* v_res_593_;
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_578_, v_i_579_, v_bs_580_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5___boxed(lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_bs_596_){
_start:
{
size_t v_sz_boxed_597_; size_t v_i_boxed_598_; lean_object* v_res_599_; 
v_sz_boxed_597_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_598_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_boxed_597_, v_i_boxed_598_, v_bs_596_);
return v_res_599_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(lean_object* v_bs_600_, lean_object* v_k_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_sz_607_ = lean_array_size(v_bs_600_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_607_, v___x_608_, v_bs_600_);
v___x_610_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v___x_609_, v_k_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_600_ = stack[0].m_obj;
lean_object* v_k_601_ = stack[1].m_obj;
lean_object* v___y_602_ = stack[2].m_obj;
lean_object* v___y_603_ = stack[3].m_obj;
lean_object* v___y_604_ = stack[4].m_obj;
lean_object* v___y_605_ = stack[5].m_obj;
lean_object* v_res_611_;
v_res_611_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_600_, v_k_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg___boxed(lean_object* v_bs_612_, lean_object* v_k_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_612_, v_k_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_619_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(lean_object* v_00_u03b1_620_, lean_object* v_bs_621_, lean_object* v_k_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_621_, v_k_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_621_ = stack[1].m_obj;
lean_object* v_k_622_ = stack[2].m_obj;
lean_object* v___y_623_ = stack[3].m_obj;
lean_object* v___y_624_ = stack[4].m_obj;
lean_object* v___y_625_ = stack[5].m_obj;
lean_object* v___y_626_ = stack[6].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(lean_box(0), v_bs_621_, v_k_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed(lean_object* v_00_u03b1_630_, lean_object* v_bs_631_, lean_object* v_k_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(v_00_u03b1_630_, v_bs_631_, v_k_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(lean_object* v_name_642_, lean_object* v_us_643_, lean_object* v_xs1_644_, lean_object* v_xs2_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1));
lean_inc(v_us_643_);
lean_inc(v_name_642_);
v___x_653_ = l_Lean_mkConst(v_name_642_, v_us_643_);
lean_inc_ref(v___x_653_);
lean_inc_ref_n(v_xs2_645_, 2);
lean_inc_ref(v_xs1_644_);
v___f_654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed), 11, 5);
lean_closure_set(v___f_654_, 0, v_name_642_);
lean_closure_set(v___f_654_, 1, v_us_643_);
lean_closure_set(v___f_654_, 2, v_xs1_644_);
lean_closure_set(v___f_654_, 3, v_xs2_645_);
lean_closure_set(v___f_654_, 4, v___x_653_);
v___x_655_ = l_Lean_mkAppN(v___x_653_, v_xs1_644_);
v___x_656_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed), 9, 4);
lean_closure_set(v___x_656_, 0, lean_box(0));
lean_closure_set(v___x_656_, 1, v___x_652_);
lean_closure_set(v___x_656_, 2, v___x_655_);
lean_closure_set(v___x_656_, 3, v___f_654_);
v___x_657_ = lean_alloc_closure((void*)(l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed), 8, 3);
lean_closure_set(v___x_657_, 0, lean_box(0));
lean_closure_set(v___x_657_, 1, v_xs2_645_);
lean_closure_set(v___x_657_, 2, v___x_656_);
v___x_658_ = lean_alloc_closure((void*)(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed), 8, 3);
lean_closure_set(v___x_658_, 0, lean_box(0));
lean_closure_set(v___x_658_, 1, v_xs2_645_);
lean_closure_set(v___x_658_, 2, v___x_657_);
v___x_659_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_xs1_644_, v___x_658_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_659_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_642_ = stack[0].m_obj;
lean_object* v_us_643_ = stack[1].m_obj;
lean_object* v_xs1_644_ = stack[2].m_obj;
lean_object* v_xs2_645_ = stack[3].m_obj;
lean_object* v_x_646_ = stack[4].m_obj;
lean_object* v___y_647_ = stack[5].m_obj;
lean_object* v___y_648_ = stack[6].m_obj;
lean_object* v___y_649_ = stack[7].m_obj;
lean_object* v___y_650_ = stack[8].m_obj;
lean_object* v_res_660_;
v_res_660_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(v_name_642_, v_us_643_, v_xs1_644_, v_xs2_645_, v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed(lean_object* v_name_661_, lean_object* v_us_662_, lean_object* v_xs1_663_, lean_object* v_xs2_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(v_name_661_, v_us_662_, v_xs1_663_, v_xs2_664_, v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_x_665_);
return v_res_671_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(lean_object* v_name_672_, lean_object* v_us_673_, lean_object* v_type_674_, lean_object* v___x_675_, lean_object* v_xs1_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___f_683_; uint8_t v___x_684_; lean_object* v___x_685_; 
v___f_683_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed), 10, 3);
lean_closure_set(v___f_683_, 0, v_name_672_);
lean_closure_set(v___f_683_, 1, v_us_673_);
lean_closure_set(v___f_683_, 2, v_xs1_676_);
v___x_684_ = 0;
v___x_685_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_674_, v___x_675_, v___f_683_, v___x_684_, v___x_684_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_685_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_672_ = stack[0].m_obj;
lean_object* v_us_673_ = stack[1].m_obj;
lean_object* v_type_674_ = stack[2].m_obj;
lean_object* v___x_675_ = stack[3].m_obj;
lean_object* v_xs1_676_ = stack[4].m_obj;
lean_object* v_x_677_ = stack[5].m_obj;
lean_object* v___y_678_ = stack[6].m_obj;
lean_object* v___y_679_ = stack[7].m_obj;
lean_object* v___y_680_ = stack[8].m_obj;
lean_object* v___y_681_ = stack[9].m_obj;
lean_object* v_res_686_;
v_res_686_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(v_name_672_, v_us_673_, v_type_674_, v___x_675_, v_xs1_676_, v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed(lean_object* v_name_687_, lean_object* v_us_688_, lean_object* v_type_689_, lean_object* v___x_690_, lean_object* v_xs1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(v_name_687_, v_us_688_, v_type_689_, v___x_690_, v_xs1_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v_x_692_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
if (lean_obj_tag(v_a_699_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = l_List_reverse___redArg(v_a_700_);
return v___x_701_;
}
else
{
lean_object* v_head_702_; lean_object* v_tail_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_head_702_ = lean_ctor_get(v_a_699_, 0);
v_tail_703_ = lean_ctor_get(v_a_699_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_705_ = v_a_699_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_tail_703_);
lean_inc(v_head_702_);
lean_dec(v_a_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_mkLevelParam(v_head_702_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v_a_700_);
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_a_700_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_a_699_ = v_tail_703_;
v_a_700_ = v___x_709_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_713_, lean_object* v_indVal_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_toConstantVal_720_; lean_object* v_numParams_721_; lean_object* v_numIndices_722_; lean_object* v_name_723_; lean_object* v_levelParams_724_; lean_object* v_type_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_802_; 
v_toConstantVal_720_ = lean_ctor_get(v_indVal_714_, 0);
lean_inc_ref(v_toConstantVal_720_);
v_numParams_721_ = lean_ctor_get(v_indVal_714_, 1);
lean_inc(v_numParams_721_);
v_numIndices_722_ = lean_ctor_get(v_indVal_714_, 2);
lean_inc(v_numIndices_722_);
lean_dec_ref(v_indVal_714_);
v_name_723_ = lean_ctor_get(v_toConstantVal_720_, 0);
v_levelParams_724_ = lean_ctor_get(v_toConstantVal_720_, 1);
v_type_725_ = lean_ctor_get(v_toConstantVal_720_, 2);
v_isSharedCheck_802_ = !lean_is_exclusive(v_toConstantVal_720_);
if (v_isSharedCheck_802_ == 0)
{
v___x_727_ = v_toConstantVal_720_;
v_isShared_728_ = v_isSharedCheck_802_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_type_725_);
lean_inc(v_levelParams_724_);
lean_inc(v_name_723_);
lean_dec(v_toConstantVal_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_802_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v_us_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___f_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_729_ = lean_box(0);
lean_inc(v_levelParams_724_);
v_us_730_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(v_levelParams_724_, v___x_729_);
v___x_731_ = lean_nat_add(v_numParams_721_, v_numIndices_722_);
lean_dec(v_numIndices_722_);
lean_dec(v_numParams_721_);
lean_inc(v___x_731_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_inc_ref(v___x_732_);
lean_inc_ref(v_type_725_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed), 11, 4);
lean_closure_set(v___f_733_, 0, v_name_723_);
lean_closure_set(v___f_733_, 1, v_us_730_);
lean_closure_set(v___f_733_, 2, v_type_725_);
lean_closure_set(v___f_733_, 3, v___x_732_);
v___x_734_ = 0;
v___x_735_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_725_, v___x_732_, v___f_733_, v___x_734_, v___x_734_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc_n(v_a_736_, 2);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_box(0);
v___x_738_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_736_, v___x_737_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Expr_mvarId_x21(v_a_739_);
v___x_741_ = lean_unsigned_to_nat(2u);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v___x_731_, v___x_742_);
lean_dec(v___x_731_);
v___x_744_ = lean_nat_mul(v___x_741_, v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = l_Lean_Meta_introNCore(v___x_740_, v___x_744_, v___x_729_, v___x_734_, v___x_734_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_snd_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_776_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v_snd_747_ = lean_ctor_get(v_a_746_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_a_746_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_a_746_, 0);
lean_dec(v_unused_777_);
v___x_749_ = v_a_746_;
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snd_747_);
lean_dec(v_a_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_snd_747_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref_known(v___x_751_, 1);
v___x_752_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_a_739_, v_a_716_);
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_767_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_767_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_767_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
lean_inc(v_thmName_713_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 2, v_a_736_);
lean_ctor_set(v___x_727_, 0, v_thmName_713_);
v___x_758_ = v___x_727_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_thmName_713_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_levelParams_724_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_a_736_);
v___x_758_ = v_reuseFailAlloc_766_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
lean_ctor_set(v___x_749_, 1, v___x_729_);
lean_ctor_set(v___x_749_, 0, v_thmName_713_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_thmName_713_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_729_);
v___x_760_ = v_reuseFailAlloc_765_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v_a_753_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_763_ = v___x_755_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
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
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_749_);
lean_dec(v_a_739_);
lean_dec(v_a_736_);
lean_del_object(v___x_727_);
lean_dec(v_levelParams_724_);
lean_dec(v_thmName_713_);
v_a_768_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_751_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_751_);
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
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_a_739_);
lean_dec(v_a_736_);
lean_del_object(v___x_727_);
lean_dec(v_levelParams_724_);
lean_dec(v_thmName_713_);
v_a_778_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_745_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_745_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_a_736_);
lean_dec(v___x_731_);
lean_del_object(v___x_727_);
lean_dec(v_levelParams_724_);
lean_dec(v_thmName_713_);
v_a_786_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_738_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_738_);
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
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v___x_731_);
lean_del_object(v___x_727_);
lean_dec(v_levelParams_724_);
lean_dec(v_thmName_713_);
v_a_794_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_735_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_735_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_713_ = stack[0].m_obj;
lean_object* v_indVal_714_ = stack[1].m_obj;
lean_object* v_a_715_ = stack[2].m_obj;
lean_object* v_a_716_ = stack[3].m_obj;
lean_object* v_a_717_ = stack[4].m_obj;
lean_object* v_a_718_ = stack[5].m_obj;
lean_object* v_res_803_;
v_res_803_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_713_, v_indVal_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
stack->m_obj
 = v_res_803_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_804_, lean_object* v_indVal_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_804_, v_indVal_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_811_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(lean_object* v_00_u03b1_812_, lean_object* v_name_813_, uint8_t v_bi_814_, lean_object* v_type_815_, lean_object* v_k_816_, uint8_t v_kind_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_813_, v_bi_814_, v_type_815_, v_k_816_, v_kind_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_813_ = stack[1].m_obj;
uint8_t v_bi_814_ = stack[2].m_num;
lean_object* v_type_815_ = stack[3].m_obj;
lean_object* v_k_816_ = stack[4].m_obj;
uint8_t v_kind_817_ = stack[5].m_num;
lean_object* v___y_818_ = stack[6].m_obj;
lean_object* v___y_819_ = stack[7].m_obj;
lean_object* v___y_820_ = stack[8].m_obj;
lean_object* v___y_821_ = stack[9].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(lean_box(0), v_name_813_, v_bi_814_, v_type_815_, v_k_816_, v_kind_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b1_825_, lean_object* v_name_826_, lean_object* v_bi_827_, lean_object* v_type_828_, lean_object* v_k_829_, lean_object* v_kind_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_bi_boxed_836_; uint8_t v_kind_boxed_837_; lean_object* v_res_838_; 
v_bi_boxed_836_ = lean_unbox(v_bi_827_);
v_kind_boxed_837_ = lean_unbox(v_kind_830_);
v_res_838_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(v_00_u03b1_825_, v_name_826_, v_bi_boxed_836_, v_type_828_, v_k_829_, v_kind_boxed_837_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_838_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(lean_object* v_00_u03b1_839_, lean_object* v_bs_840_, lean_object* v_k_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_840_, v_k_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_840_ = stack[1].m_obj;
lean_object* v_k_841_ = stack[2].m_obj;
lean_object* v___y_842_ = stack[3].m_obj;
lean_object* v___y_843_ = stack[4].m_obj;
lean_object* v___y_844_ = stack[5].m_obj;
lean_object* v___y_845_ = stack[6].m_obj;
lean_object* v_res_848_;
v_res_848_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(lean_box(0), v_bs_840_, v_k_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___boxed(lean_object* v_00_u03b1_849_, lean_object* v_bs_850_, lean_object* v_k_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(v_00_u03b1_849_, v_bs_850_, v_k_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_bs_850_);
return v_res_857_;
}
}
uint8_t l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(lean_object* v_env_858_, lean_object* v_n_859_){
_start:
{
if (lean_obj_tag(v_n_859_) == 1)
{
lean_object* v_pre_860_; lean_object* v_str_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_pre_860_ = lean_ctor_get(v_n_859_, 0);
lean_inc(v_pre_860_);
v_str_861_ = lean_ctor_get(v_n_859_, 1);
lean_inc_ref(v_str_861_);
lean_dec_ref_known(v_n_859_, 2);
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0));
v___x_863_ = lean_string_dec_eq(v_str_861_, v___x_862_);
lean_dec_ref(v_str_861_);
if (v___x_863_ == 0)
{
lean_dec(v_pre_860_);
lean_dec_ref(v_env_858_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_isCtorIdxCore_x3f(v_env_858_, v_pre_860_);
if (lean_obj_tag(v___x_864_) == 0)
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
else
{
lean_dec_ref_known(v___x_864_, 1);
return v___x_863_;
}
}
}
else
{
uint8_t v___x_866_; 
lean_dec(v_n_859_);
lean_dec_ref(v_env_858_);
v___x_866_ = 0;
return v___x_866_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_858_ = stack[0].m_obj;
lean_object* v_n_859_ = stack[1].m_obj;
uint8_t v_res_867_;
v_res_867_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(v_env_858_, v_n_859_);
stack->m_num = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object* v_env_868_, lean_object* v_n_869_){
_start:
{
uint8_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(v_env_868_, v_n_869_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_874_; lean_object* v___x_875_; 
v___f_874_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_));
v___x_875_ = l_Lean_registerReservedNamePredicate(v___f_874_);
return v___x_875_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_876_;
v_res_876_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
return v_res_878_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v_env_883_; lean_object* v_toConstantVal_884_; lean_object* v_value_885_; lean_object* v_all_886_; uint8_t v___y_888_; lean_object* v_type_896_; uint8_t v___x_897_; 
v___x_882_ = lean_st_ref_get(v___y_880_);
v_env_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc_ref_n(v_env_883_, 2);
lean_dec(v___x_882_);
v_toConstantVal_884_ = lean_ctor_get(v_thm_879_, 0);
v_value_885_ = lean_ctor_get(v_thm_879_, 1);
v_all_886_ = lean_ctor_get(v_thm_879_, 2);
v_type_896_ = lean_ctor_get(v_toConstantVal_884_, 2);
v___x_897_ = l_Lean_Environment_hasUnsafe(v_env_883_, v_type_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_Environment_hasUnsafe(v_env_883_, v_value_885_);
v___y_888_ = v___x_898_;
goto v___jp_887_;
}
else
{
lean_dec_ref(v_env_883_);
v___y_888_ = v___x_897_;
goto v___jp_887_;
}
v___jp_887_:
{
if (v___y_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_889_, 0, v_thm_879_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_all_886_);
lean_inc_ref(v_value_885_);
lean_inc_ref(v_toConstantVal_884_);
lean_dec_ref(v_thm_879_);
v___x_891_ = lean_box(0);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_893_, 0, v_toConstantVal_884_);
lean_ctor_set(v___x_893_, 1, v_value_885_);
lean_ctor_set(v___x_893_, 2, v___x_891_);
lean_ctor_set(v___x_893_, 3, v_all_886_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*4, v___x_892_);
v___x_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_879_ = stack[0].m_obj;
lean_object* v___y_880_ = stack[1].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_879_, v___y_880_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_900_, v___y_901_);
lean_dec(v___y_901_);
return v_res_903_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(lean_object* v_thm_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_904_, v___y_908_);
return v___x_910_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_904_ = stack[0].m_obj;
lean_object* v___y_905_ = stack[1].m_obj;
lean_object* v___y_906_ = stack[2].m_obj;
lean_object* v___y_907_ = stack[3].m_obj;
lean_object* v___y_908_ = stack[4].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(v_thm_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(v_thm_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_918_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object* v_name_919_, lean_object* v_val_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_919_, v_val_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; lean_object* v_a_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_a_927_, v___y_924_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = 0;
v___x_931_ = l_Lean_addDecl(v_a_929_, v___x_930_, v___y_923_, v___y_924_);
return v___x_931_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_926_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_926_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_name_919_ = stack[0].m_obj;
lean_object* v_val_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v_res_940_;
v_res_940_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v_name_919_, v_val_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v_name_941_, lean_object* v_val_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v_name_941_, v_val_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_948_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_unsigned_to_nat(32u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
size_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((size_t)5ULL);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_unsigned_to_nat(32u);
v___x_958_ = lean_mk_empty_array_with_capacity(v___x_957_);
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
lean_ctor_set(v___x_960_, 2, v___x_956_);
lean_ctor_set(v___x_960_, 3, v___x_956_);
lean_ctor_set_usize(v___x_960_, 4, v___x_955_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_box(1);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
lean_ctor_set(v___x_964_, 2, v___x_961_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_968_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
lean_ctor_set(v___x_970_, 4, v___x_968_);
lean_ctor_set(v___x_970_, 5, v___x_968_);
lean_ctor_set(v___x_970_, 6, v___x_968_);
lean_ctor_set(v___x_970_, 7, v___x_968_);
lean_ctor_set(v___x_970_, 8, v___x_968_);
lean_ctor_set(v___x_970_, 9, v___x_968_);
lean_ctor_set(v___x_970_, 10, v___x_968_);
lean_ctor_set(v___x_970_, 11, v___x_967_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_972_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_ctor_set(v___x_972_, 3, v___x_971_);
lean_ctor_set(v___x_972_, 4, v___x_971_);
lean_ctor_set(v___x_972_, 5, v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
lean_ctor_set(v___x_974_, 4, v___x_973_);
return v___x_974_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(lean_object* v___x_975_, lean_object* v_name_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
if (lean_obj_tag(v_name_976_) == 1)
{
lean_object* v_pre_984_; lean_object* v_str_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_pre_984_ = lean_ctor_get(v_name_976_, 0);
lean_inc(v_pre_984_);
v_str_985_ = lean_ctor_get(v_name_976_, 1);
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0));
v___x_987_ = lean_string_dec_eq(v_str_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref_known(v_name_976_, 2);
lean_dec(v_pre_984_);
lean_dec(v___x_975_);
goto v___jp_980_;
}
else
{
lean_object* v___x_988_; lean_object* v_env_989_; lean_object* v___x_990_; 
v___x_988_ = lean_st_ref_get(v___y_978_);
v_env_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_env_989_);
lean_dec(v___x_988_);
lean_inc(v_pre_984_);
v___x_990_ = l_Lean_isCtorIdxCore_x3f(v_env_989_, v_pre_984_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___f_992_; uint8_t v___x_993_; uint8_t v___x_994_; uint8_t v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; uint64_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
lean_inc_ref(v_name_976_);
v___f_992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_992_, 0, v_name_976_);
lean_closure_set(v___f_992_, 1, v_val_991_);
v___x_993_ = 0;
v___x_994_ = 1;
v___x_995_ = 0;
v___x_996_ = 2;
v___x_997_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_997_, 0, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 1, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 2, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 3, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 4, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 5, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 6, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 7, v___x_993_);
lean_ctor_set_uint8(v___x_997_, 8, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 9, v___x_994_);
lean_ctor_set_uint8(v___x_997_, 10, v___x_995_);
lean_ctor_set_uint8(v___x_997_, 11, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 12, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 13, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 14, v___x_996_);
lean_ctor_set_uint8(v___x_997_, 15, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 16, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 17, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 18, v___x_987_);
lean_ctor_set_uint8(v___x_997_, 19, v___x_993_);
v___x_998_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_997_);
v___x_999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set_uint64(v___x_999_, sizeof(void*)*1, v___x_998_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_));
v___x_1004_ = lean_box(0);
lean_inc(v___x_975_);
v___x_1005_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1005_, 0, v___x_999_);
lean_ctor_set(v___x_1005_, 1, v___x_975_);
lean_ctor_set(v___x_1005_, 2, v___x_1002_);
lean_ctor_set(v___x_1005_, 3, v___x_1003_);
lean_ctor_set(v___x_1005_, 4, v___x_1004_);
lean_ctor_set(v___x_1005_, 5, v___x_1000_);
lean_ctor_set(v___x_1005_, 6, v___x_1004_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*7, v___x_993_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*7 + 1, v___x_993_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*7 + 2, v___x_993_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*7 + 3, v___x_987_);
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_1008_ = lean_obj_once(&l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_, &l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
v___x_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
lean_ctor_set(v___x_1009_, 2, v___x_975_);
lean_ctor_set(v___x_1009_, 3, v___x_1001_);
lean_ctor_set(v___x_1009_, 4, v___x_1008_);
v___x_1010_ = lean_st_mk_ref(v___x_1009_);
v___x_1011_ = l_Lean_Meta_realizeConst(v_pre_984_, v_name_976_, v___f_992_, v___x_1005_, v___x_1010_, v___y_977_, v___y_978_);
lean_dec_ref_known(v___x_1005_, 7);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1021_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = lean_st_ref_get(v___x_1010_);
lean_dec(v___x_1010_);
lean_dec(v___x_1015_);
v___x_1016_ = lean_box(v___x_987_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1016_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v___x_1010_);
v_a_1022_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1011_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1011_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v___x_990_);
lean_dec_ref_known(v_name_976_, 2);
lean_dec(v_pre_984_);
lean_dec(v___x_975_);
v___x_1030_ = 0;
v___x_1031_ = lean_box(v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
else
{
lean_dec(v_name_976_);
lean_dec(v___x_975_);
goto v___jp_980_;
}
v___jp_980_:
{
uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = 0;
v___x_982_ = lean_box(v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_975_ = stack[0].m_obj;
lean_object* v_name_976_ = stack[1].m_obj;
lean_object* v___y_977_ = stack[2].m_obj;
lean_object* v___y_978_ = stack[3].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v___x_975_, v_name_976_, v___y_977_, v___y_978_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v___x_1034_, lean_object* v_name_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v___x_1034_, v_name_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1039_;
}
}
lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; 
v___f_1043_ = ((lean_object*)(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_));
v___x_1044_ = l_Lean_registerReservedNameAction(v___f_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1045_;
v_res_1045_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
return v_res_1047_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
