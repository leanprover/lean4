// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: public import Lean.Meta.Tactic.Rename public import Lean.Elab.PreDefinition.TerminationMeasure public import Lean.Elab.PreDefinition.FixedParams public import Lean.Meta.ArgsPacker
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
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Elab.PreDefinition.WF.Rel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Elab.WF.checkCodomains"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: xs.size = arity\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "The termination measure's type must not depend on the "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "function's varying parameters, but "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "'s termination measure does:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Try using `sizeOf` explicitly"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "The termination measures of mutually recursive functions "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "must have the same return type, but the termination measure of "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " has type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "while the termination measure of "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_WF_checkCodomains___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_WF_checkCodomains___closed__0 = (const lean_object*)&l_Lean_Elab_WF_checkCodomains___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_checkCodomains___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_checkCodomains___closed__1 = (const lean_object*)&l_Lean_Elab_WF_checkCodomains___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invImage"};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 194, 127, 152, 147, 1, 182, 44)}};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_6826__overap_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0, &l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0);
v___x_6826__overap_11_ = lean_panic_fn_borrowed(v___x_10_, v_msg_2_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_12_ = lean_apply_7(v___x_6826__overap_11_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(lean_object* v_msg_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v_msg_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(lean_object* v_k_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v_b_25_, lean_object* v_c_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; 
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
v___x_32_ = lean_apply_9(v_k_22_, v_b_25_, v_c_26_, v___y_23_, v___y_24_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, lean_box(0));
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(lean_object* v_k_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v_b_36_, lean_object* v_c_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(v_k_33_, v___y_34_, v___y_35_, v_b_36_, v_c_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(lean_object* v_type_44_, lean_object* v_maxFVars_x3f_45_, lean_object* v_k_46_, uint8_t v_cleanupAnnotations_47_, uint8_t v_whnfType_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; 
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
v___f_56_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_56_, 0, v_k_46_);
lean_closure_set(v___f_56_, 1, v___y_49_);
lean_closure_set(v___f_56_, 2, v___y_50_);
v___x_57_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_44_, v_maxFVars_x3f_45_, v___f_56_, v_cleanupAnnotations_47_, v_whnfType_48_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_57_) == 0)
{
return v___x_57_;
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(lean_object* v_type_66_, lean_object* v_maxFVars_x3f_67_, lean_object* v_k_68_, lean_object* v_cleanupAnnotations_69_, lean_object* v_whnfType_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_78_; uint8_t v_whnfType_boxed_79_; lean_object* v_res_80_; 
v_cleanupAnnotations_boxed_78_ = lean_unbox(v_cleanupAnnotations_69_);
v_whnfType_boxed_79_ = lean_unbox(v_whnfType_70_);
v_res_80_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_type_66_, v_maxFVars_x3f_67_, v_k_68_, v_cleanupAnnotations_boxed_78_, v_whnfType_boxed_79_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_object* v_00_u03b1_81_, lean_object* v_type_82_, lean_object* v_maxFVars_x3f_83_, lean_object* v_k_84_, uint8_t v_cleanupAnnotations_85_, uint8_t v_whnfType_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_type_82_, v_maxFVars_x3f_83_, v_k_84_, v_cleanupAnnotations_85_, v_whnfType_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(lean_object* v_00_u03b1_95_, lean_object* v_type_96_, lean_object* v_maxFVars_x3f_97_, lean_object* v_k_98_, lean_object* v_cleanupAnnotations_99_, lean_object* v_whnfType_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_108_; uint8_t v_whnfType_boxed_109_; lean_object* v_res_110_; 
v_cleanupAnnotations_boxed_108_ = lean_unbox(v_cleanupAnnotations_99_);
v_whnfType_boxed_109_ = lean_unbox(v_whnfType_100_);
v_res_110_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(v_00_u03b1_95_, v_type_96_, v_maxFVars_x3f_97_, v_k_98_, v_cleanupAnnotations_boxed_108_, v_whnfType_boxed_109_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(lean_object* v_a_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
v___x_117_ = l_Lean_instBEqFVarId_beq(v_a_111_, v___x_116_);
if (v___x_117_ == 0)
{
size_t v___x_118_; size_t v___x_119_; 
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_113_, v___x_118_);
v_i_113_ = v___x_119_;
goto _start;
}
else
{
return v___x_117_;
}
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(lean_object* v_a_122_, lean_object* v_as_123_, lean_object* v_i_124_, lean_object* v_stop_125_){
_start:
{
size_t v_i_boxed_126_; size_t v_stop_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_i_boxed_126_ = lean_unbox_usize(v_i_124_);
lean_dec(v_i_124_);
v_stop_boxed_127_ = lean_unbox_usize(v_stop_125_);
lean_dec(v_stop_125_);
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_122_, v_as_123_, v_i_boxed_126_, v_stop_boxed_127_);
lean_dec_ref(v_as_123_);
lean_dec(v_a_122_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(lean_object* v_as_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_array_get_size(v_as_130_);
v___x_134_ = lean_nat_dec_lt(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_133_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_131_, v_as_130_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(lean_object* v_as_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v_as_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_as_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(lean_object* v___x_142_, lean_object* v_e_143_){
_start:
{
uint8_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = l_Lean_Expr_hasFVar(v_e_143_);
v___x_145_ = lean_bool_not(v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; lean_object* v_d_148_; lean_object* v_b_149_; 
v___x_146_ = 1;
switch(lean_obj_tag(v_e_143_))
{
case 7:
{
lean_object* v_binderType_152_; lean_object* v_body_153_; 
v_binderType_152_ = lean_ctor_get(v_e_143_, 1);
v_body_153_ = lean_ctor_get(v_e_143_, 2);
v_d_148_ = v_binderType_152_;
v_b_149_ = v_body_153_;
goto v___jp_147_;
}
case 6:
{
lean_object* v_binderType_154_; lean_object* v_body_155_; 
v_binderType_154_ = lean_ctor_get(v_e_143_, 1);
v_body_155_ = lean_ctor_get(v_e_143_, 2);
v_d_148_ = v_binderType_154_;
v_b_149_ = v_body_155_;
goto v___jp_147_;
}
case 10:
{
lean_object* v_expr_156_; 
v_expr_156_ = lean_ctor_get(v_e_143_, 1);
v_e_143_ = v_expr_156_;
goto _start;
}
case 8:
{
lean_object* v_type_158_; lean_object* v_value_159_; lean_object* v_body_160_; uint8_t v___x_161_; 
v_type_158_ = lean_ctor_get(v_e_143_, 1);
v_value_159_ = lean_ctor_get(v_e_143_, 2);
v_body_160_ = lean_ctor_get(v_e_143_, 3);
v___x_161_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_type_158_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_value_159_);
if (v___x_162_ == 0)
{
v_e_143_ = v_body_160_;
goto _start;
}
else
{
return v___x_146_;
}
}
else
{
return v___x_146_;
}
}
case 5:
{
lean_object* v_fn_164_; lean_object* v_arg_165_; uint8_t v___x_166_; 
v_fn_164_ = lean_ctor_get(v_e_143_, 0);
v_arg_165_ = lean_ctor_get(v_e_143_, 1);
v___x_166_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_fn_164_);
if (v___x_166_ == 0)
{
v_e_143_ = v_arg_165_;
goto _start;
}
else
{
return v___x_146_;
}
}
case 11:
{
lean_object* v_struct_168_; 
v_struct_168_ = lean_ctor_get(v_e_143_, 2);
v_e_143_ = v_struct_168_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_170_; uint8_t v___x_171_; 
v_fvarId_170_ = lean_ctor_get(v_e_143_, 0);
v___x_171_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v___x_142_, v_fvarId_170_);
return v___x_171_;
}
default: 
{
return v___x_145_;
}
}
v___jp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_d_148_);
if (v___x_150_ == 0)
{
v_e_143_ = v_b_149_;
goto _start;
}
else
{
return v___x_146_;
}
}
}
else
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object* v___x_173_, lean_object* v_e_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_173_, v_e_174_);
lean_dec_ref(v_e_174_);
lean_dec_ref(v___x_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t v_sz_177_, size_t v_i_178_, lean_object* v_bs_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_180_ == 0)
{
return v_bs_179_;
}
else
{
lean_object* v_v_181_; lean_object* v___x_182_; lean_object* v_bs_x27_183_; lean_object* v___x_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v_v_181_ = lean_array_uget(v_bs_179_, v_i_178_);
v___x_182_ = lean_unsigned_to_nat(0u);
v_bs_x27_183_ = lean_array_uset(v_bs_179_, v_i_178_, v___x_182_);
v___x_184_ = l_Lean_Expr_fvarId_x21(v_v_181_);
lean_dec(v_v_181_);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_178_, v___x_185_);
v___x_187_ = lean_array_uset(v_bs_x27_183_, v_i_178_, v___x_184_);
v_i_178_ = v___x_186_;
v_bs_179_ = v___x_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object* v_sz_189_, lean_object* v_i_190_, lean_object* v_bs_191_){
_start:
{
size_t v_sz_boxed_192_; size_t v_i_boxed_193_; lean_object* v_res_194_; 
v_sz_boxed_192_ = lean_unbox_usize(v_sz_189_);
lean_dec(v_sz_189_);
v_i_boxed_193_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_boxed_192_, v_i_boxed_193_, v_bs_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v_mctx_204_; lean_object* v_lctx_205_; lean_object* v_options_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_201_ = lean_st_ref_get(v___y_199_);
v_env_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_env_202_);
lean_dec(v___x_201_);
v___x_203_ = lean_st_ref_get(v___y_197_);
v_mctx_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_mctx_204_);
lean_dec(v___x_203_);
v_lctx_205_ = lean_ctor_get(v___y_196_, 2);
v_options_206_ = lean_ctor_get(v___y_198_, 2);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_lctx_205_);
v___x_207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_207_, 0, v_env_202_);
lean_ctor_set(v___x_207_, 1, v_mctx_204_);
lean_ctor_set(v___x_207_, 2, v_lctx_205_);
lean_ctor_set(v___x_207_, 3, v_options_206_);
v___x_208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_msgData_195_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object* v_msgData_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object* v_opts_217_, lean_object* v_opt_218_){
_start:
{
lean_object* v_name_219_; lean_object* v_defValue_220_; lean_object* v_map_221_; lean_object* v___x_222_; 
v_name_219_ = lean_ctor_get(v_opt_218_, 0);
v_defValue_220_ = lean_ctor_get(v_opt_218_, 1);
v_map_221_ = lean_ctor_get(v_opts_217_, 0);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_221_, v_name_219_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
v___x_223_ = lean_unbox(v_defValue_220_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_222_, 1);
if (lean_obj_tag(v_val_224_) == 1)
{
uint8_t v_v_225_; 
v_v_225_ = lean_ctor_get_uint8(v_val_224_, 0);
lean_dec_ref_known(v_val_224_, 0);
return v_v_225_;
}
else
{
uint8_t v___x_226_; 
lean_dec(v_val_224_);
v___x_226_ = lean_unbox(v_defValue_220_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object* v_opts_227_, lean_object* v_opt_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_227_, v_opt_228_);
lean_dec_ref(v_opt_228_);
lean_dec_ref(v_opts_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(1);
v___x_232_ = l_Lean_MessageData_ofFormat(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2));
v___x_237_ = l_Lean_MessageData_ofFormat(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
return v_x_238_;
}
else
{
lean_object* v_head_240_; lean_object* v_tail_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_263_; 
v_head_240_ = lean_ctor_get(v_x_239_, 0);
v_tail_241_ = lean_ctor_get(v_x_239_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_263_ == 0)
{
v___x_243_ = v_x_239_;
v_isShared_244_ = v_isSharedCheck_263_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_tail_241_);
lean_inc(v_head_240_);
lean_dec(v_x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_263_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_before_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_261_; 
v_before_245_ = lean_ctor_get(v_head_240_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_head_240_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_head_240_, 1);
lean_dec(v_unused_262_);
v___x_247_ = v_head_240_;
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_before_245_);
lean_dec(v_head_240_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 7);
lean_ctor_set(v___x_247_, 1, v___x_249_);
lean_ctor_set(v___x_247_, 0, v_x_238_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_x_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_260_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 7);
lean_ctor_set(v___x_243_, 1, v___x_252_);
lean_ctor_set(v___x_243_, 0, v___x_251_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_259_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_MessageData_ofSyntax(v_before_245_);
v___x_256_ = l_Lean_indentD(v___x_255_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_254_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v_x_238_ = v___x_257_;
v_x_239_ = v_tail_241_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1));
v___x_268_ = l_Lean_MessageData_ofFormat(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object* v_msgData_269_, lean_object* v_macroStack_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_options_273_; lean_object* v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v_options_273_ = lean_ctor_get(v___y_271_, 2);
v___x_274_ = l_Lean_Elab_pp_macroStack;
v___x_275_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_options_273_, v___x_274_);
v___x_276_ = lean_bool_not(v___x_275_);
if (v___x_276_ == 0)
{
if (lean_obj_tag(v_macroStack_270_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_msgData_269_);
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_after_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_294_; 
v_head_278_ = lean_ctor_get(v_macroStack_270_, 0);
lean_inc(v_head_278_);
v_after_279_ = lean_ctor_get(v_head_278_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_head_278_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_head_278_, 0);
lean_dec(v_unused_295_);
v___x_281_ = v_head_278_;
v_isShared_282_ = v_isSharedCheck_294_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_after_279_);
lean_dec(v_head_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_294_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 7);
lean_ctor_set(v___x_281_, 1, v___x_283_);
lean_ctor_set(v___x_281_, 0, v_msgData_269_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_msgData_269_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_293_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_msgData_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_286_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_MessageData_ofSyntax(v_after_279_);
v___x_289_ = l_Lean_indentD(v___x_288_);
v_msgData_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_290_, 0, v___x_287_);
lean_ctor_set(v_msgData_290_, 1, v___x_289_);
v___x_291_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(v_msgData_290_, v_macroStack_270_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_296_; 
lean_dec(v_macroStack_270_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_msgData_269_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_297_, lean_object* v_macroStack_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_297_, v_macroStack_298_, v___y_299_);
lean_dec_ref(v___y_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_ref_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v_macroStack_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_ref_310_ = lean_ctor_get(v___y_307_, 5);
v___x_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msg_302_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
v_macroStack_313_ = lean_ctor_get(v___y_303_, 1);
v___x_314_ = l_Lean_Elab_getBetterRef(v_ref_310_, v_macroStack_313_);
lean_inc(v_macroStack_313_);
v___x_315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_a_312_, v_macroStack_313_, v___y_307_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_314_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 1);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object* v_ref_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_fileName_343_; lean_object* v_fileMap_344_; lean_object* v_options_345_; lean_object* v_currRecDepth_346_; lean_object* v_maxRecDepth_347_; lean_object* v_ref_348_; lean_object* v_currNamespace_349_; lean_object* v_openDecls_350_; lean_object* v_initHeartbeats_351_; lean_object* v_maxHeartbeats_352_; lean_object* v_quotContext_353_; lean_object* v_currMacroScope_354_; uint8_t v_diag_355_; lean_object* v_cancelTk_x3f_356_; uint8_t v_suppressElabErrors_357_; lean_object* v_inheritedTraceOptions_358_; lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_fileName_343_ = lean_ctor_get(v___y_340_, 0);
v_fileMap_344_ = lean_ctor_get(v___y_340_, 1);
v_options_345_ = lean_ctor_get(v___y_340_, 2);
v_currRecDepth_346_ = lean_ctor_get(v___y_340_, 3);
v_maxRecDepth_347_ = lean_ctor_get(v___y_340_, 4);
v_ref_348_ = lean_ctor_get(v___y_340_, 5);
v_currNamespace_349_ = lean_ctor_get(v___y_340_, 6);
v_openDecls_350_ = lean_ctor_get(v___y_340_, 7);
v_initHeartbeats_351_ = lean_ctor_get(v___y_340_, 8);
v_maxHeartbeats_352_ = lean_ctor_get(v___y_340_, 9);
v_quotContext_353_ = lean_ctor_get(v___y_340_, 10);
v_currMacroScope_354_ = lean_ctor_get(v___y_340_, 11);
v_diag_355_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*14);
v_cancelTk_x3f_356_ = lean_ctor_get(v___y_340_, 12);
v_suppressElabErrors_357_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_358_ = lean_ctor_get(v___y_340_, 13);
v_ref_359_ = l_Lean_replaceRef(v_ref_334_, v_ref_348_);
lean_inc_ref(v_inheritedTraceOptions_358_);
lean_inc(v_cancelTk_x3f_356_);
lean_inc(v_currMacroScope_354_);
lean_inc(v_quotContext_353_);
lean_inc(v_maxHeartbeats_352_);
lean_inc(v_initHeartbeats_351_);
lean_inc(v_openDecls_350_);
lean_inc(v_currNamespace_349_);
lean_inc(v_maxRecDepth_347_);
lean_inc(v_currRecDepth_346_);
lean_inc_ref(v_options_345_);
lean_inc_ref(v_fileMap_344_);
lean_inc_ref(v_fileName_343_);
v___x_360_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_360_, 0, v_fileName_343_);
lean_ctor_set(v___x_360_, 1, v_fileMap_344_);
lean_ctor_set(v___x_360_, 2, v_options_345_);
lean_ctor_set(v___x_360_, 3, v_currRecDepth_346_);
lean_ctor_set(v___x_360_, 4, v_maxRecDepth_347_);
lean_ctor_set(v___x_360_, 5, v_ref_359_);
lean_ctor_set(v___x_360_, 6, v_currNamespace_349_);
lean_ctor_set(v___x_360_, 7, v_openDecls_350_);
lean_ctor_set(v___x_360_, 8, v_initHeartbeats_351_);
lean_ctor_set(v___x_360_, 9, v_maxHeartbeats_352_);
lean_ctor_set(v___x_360_, 10, v_quotContext_353_);
lean_ctor_set(v___x_360_, 11, v_currMacroScope_354_);
lean_ctor_set(v___x_360_, 12, v_cancelTk_x3f_356_);
lean_ctor_set(v___x_360_, 13, v_inheritedTraceOptions_358_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*14, v_diag_355_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*14 + 1, v_suppressElabErrors_357_);
v___x_361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___x_360_, v___y_341_);
lean_dec_ref_known(v___x_360_, 14);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object* v_ref_362_, lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_362_, v_msg_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v_ref_362_);
return v_res_371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2));
v___x_376_ = lean_unsigned_to_nat(6u);
v___x_377_ = lean_unsigned_to_nat(33u);
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1));
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0));
v___x_380_ = l_mkPanicMessageWithDecl(v___x_379_, v___x_378_, v___x_377_, v___x_376_, v___x_375_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13));
v___x_397_ = l_Lean_MessageData_ofFormat(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object* v___x_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_ref_401_, lean_object* v_xs_402_, lean_object* v_codomain_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_xs_402_);
v___x_412_ = lean_nat_dec_eq(v___x_411_, v___x_398_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v_codomain_403_);
lean_dec_ref(v_xs_402_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
v___x_413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
v___x_414_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v___x_413_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_414_;
}
else
{
size_t v_sz_415_; size_t v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_sz_415_ = lean_array_size(v_xs_402_);
v___x_416_ = ((size_t)0ULL);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_415_, v___x_416_, v_xs_402_);
v___x_418_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_417_, v_codomain_403_);
lean_dec_ref(v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_codomain_403_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
v___x_421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
v___x_422_ = l_Lean_MessageData_ofName(v_a_399_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_indentExpr(v_a_400_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_420_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_401_, v___x_432_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_433_, 0);
lean_dec(v_unused_441_);
v___x_435_ = v___x_433_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_433_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_codomain_403_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_codomain_403_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_codomain_403_);
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object* v___x_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_ref_453_, lean_object* v_xs_454_, lean_object* v_codomain_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_450_, v_a_451_, v_a_452_, v_ref_453_, v_xs_454_, v_codomain_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_ref_453_);
lean_dec(v___x_450_);
return v_res_463_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Array_instInhabited(lean_box(0));
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object* v_fixedParamPerms_465_, lean_object* v_fixedArgs_466_, lean_object* v_as_467_, size_t v_sz_468_, size_t v_i_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_469_, v_sz_468_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_fixedArgs_466_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_b_470_);
return v___x_479_;
}
else
{
lean_object* v_snd_480_; lean_object* v_snd_481_; lean_object* v_snd_482_; lean_object* v_fst_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_630_; 
v_snd_480_ = lean_ctor_get(v_b_470_, 1);
lean_inc(v_snd_480_);
v_snd_481_ = lean_ctor_get(v_snd_480_, 1);
lean_inc(v_snd_481_);
v_snd_482_ = lean_ctor_get(v_snd_481_, 1);
lean_inc(v_snd_482_);
v_fst_483_ = lean_ctor_get(v_b_470_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_b_470_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_b_470_, 1);
lean_dec(v_unused_631_);
v___x_485_ = v_b_470_;
v_isShared_486_ = v_isSharedCheck_630_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_fst_483_);
lean_dec(v_b_470_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_630_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_fst_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_628_; 
v_fst_487_ = lean_ctor_get(v_snd_480_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_snd_480_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_snd_480_, 1);
lean_dec(v_unused_629_);
v___x_489_ = v_snd_480_;
v_isShared_490_ = v_isSharedCheck_628_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_fst_487_);
lean_dec(v_snd_480_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_628_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_fst_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_626_; 
v_fst_491_ = lean_ctor_get(v_snd_481_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_snd_481_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_snd_481_, 1);
lean_dec(v_unused_627_);
v___x_493_ = v_snd_481_;
v_isShared_494_ = v_isSharedCheck_626_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_fst_491_);
lean_dec(v_snd_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_626_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_array_495_; lean_object* v_start_496_; lean_object* v_stop_497_; uint8_t v___x_498_; 
v_array_495_ = lean_ctor_get(v_snd_482_, 0);
v_start_496_ = lean_ctor_get(v_snd_482_, 1);
v_stop_497_ = lean_ctor_get(v_snd_482_, 2);
v___x_498_ = lean_nat_dec_lt(v_start_496_, v_stop_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_500_; 
lean_dec_ref(v_fixedArgs_466_);
if (v_isShared_494_ == 0)
{
v___x_500_ = v___x_493_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_snd_482_);
v___x_500_ = v_reuseFailAlloc_508_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_500_);
v___x_502_ = v___x_489_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_507_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_502_);
v___x_504_ = v___x_485_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
}
else
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_622_; 
lean_inc(v_stop_497_);
lean_inc(v_start_496_);
lean_inc_ref(v_array_495_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_snd_482_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v_snd_482_, 2);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_snd_482_, 1);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_snd_482_, 0);
lean_dec(v_unused_625_);
v___x_510_ = v_snd_482_;
v_isShared_511_ = v_isSharedCheck_622_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_snd_482_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_622_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_array_512_; lean_object* v_start_513_; lean_object* v_stop_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v_array_512_ = lean_ctor_get(v_fst_491_, 0);
v_start_513_ = lean_ctor_get(v_fst_491_, 1);
v_stop_514_ = lean_ctor_get(v_fst_491_, 2);
v___x_515_ = lean_array_fget(v_array_495_, v_start_496_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_start_496_, v___x_516_);
lean_dec(v_start_496_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_517_);
v___x_519_ = v___x_510_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_array_495_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_stop_497_);
v___x_519_ = v_reuseFailAlloc_621_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v_start_513_, v_stop_514_);
if (v___x_520_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v___x_515_);
lean_dec_ref(v_fixedArgs_466_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_519_);
v___x_522_ = v___x_493_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_519_);
v___x_522_ = v_reuseFailAlloc_530_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_522_);
v___x_524_ = v___x_489_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_529_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_524_);
v___x_526_ = v___x_485_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_617_; 
lean_inc(v_stop_514_);
lean_inc(v_start_513_);
lean_inc_ref(v_array_512_);
v_isSharedCheck_617_ = !lean_is_exclusive(v_fst_491_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_618_ = lean_ctor_get(v_fst_491_, 2);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_fst_491_, 1);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_fst_491_, 0);
lean_dec(v_unused_620_);
v___x_532_ = v_fst_491_;
v_isShared_533_ = v_isSharedCheck_617_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_fst_491_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_617_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_next_534_; lean_object* v_upperBound_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v_next_534_ = lean_ctor_get(v_fst_487_, 0);
lean_inc(v_next_534_);
v_upperBound_535_ = lean_ctor_get(v_fst_487_, 1);
v___x_536_ = lean_array_fget(v_array_512_, v_start_513_);
v___x_537_ = lean_nat_add(v_start_513_, v___x_516_);
lean_dec(v_start_513_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_537_);
v___x_539_ = v___x_532_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_array_512_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_stop_514_);
v___x_539_ = v_reuseFailAlloc_616_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
if (lean_obj_tag(v_next_534_) == 0)
{
lean_dec(v___x_536_);
lean_dec(v___x_515_);
lean_dec_ref(v_fixedArgs_466_);
goto v___jp_540_;
}
else
{
lean_object* v_val_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_615_; 
v_val_551_ = lean_ctor_get(v_next_534_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_next_534_);
if (v_isSharedCheck_615_ == 0)
{
v___x_553_ = v_next_534_;
v_isShared_554_ = v_isSharedCheck_615_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_val_551_);
lean_dec(v_next_534_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_615_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_lt(v_val_551_, v_upperBound_535_);
if (v___x_555_ == 0)
{
lean_del_object(v___x_553_);
lean_dec(v_val_551_);
lean_dec(v___x_536_);
lean_dec(v___x_515_);
lean_dec_ref(v_fixedArgs_466_);
goto v___jp_540_;
}
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_612_; 
lean_inc(v_upperBound_535_);
lean_del_object(v___x_493_);
lean_del_object(v___x_489_);
lean_del_object(v___x_485_);
v_isSharedCheck_612_ = !lean_is_exclusive(v_fst_487_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; 
v_unused_613_ = lean_ctor_get(v_fst_487_, 1);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_fst_487_, 0);
lean_dec(v_unused_614_);
v___x_557_ = v_fst_487_;
v_isShared_558_ = v_isSharedCheck_612_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_fst_487_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_612_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_ref_559_; lean_object* v_fn_560_; lean_object* v___x_561_; 
v_ref_559_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_ref_559_);
v_fn_560_ = lean_ctor_get(v___x_515_, 1);
lean_inc_ref(v_fn_560_);
lean_dec(v___x_515_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
v___x_561_ = lean_infer_type(v_fn_560_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v_perms_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v_perms_563_ = lean_ctor_get(v_fixedParamPerms_465_, 1);
v___x_564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_565_ = lean_array_get_borrowed(v___x_564_, v_perms_563_, v_val_551_);
lean_inc_ref(v_fixedArgs_466_);
lean_inc(v___x_565_);
v___x_566_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_565_, v_a_562_, v_fixedArgs_466_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v_a_568_; lean_object* v___f_569_; lean_object* v___x_571_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_n(v_a_567_, 2);
lean_dec_ref_known(v___x_566_, 1);
v_a_568_ = lean_array_uget_borrowed(v_as_467_, v_i_469_);
lean_inc(v_a_568_);
lean_inc(v___x_536_);
v___f_569_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(v___f_569_, 0, v___x_536_);
lean_closure_set(v___f_569_, 1, v_a_568_);
lean_closure_set(v___f_569_, 2, v_a_567_);
lean_closure_set(v___f_569_, 3, v_ref_559_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_536_);
v___x_571_ = v___x_553_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_536_);
v___x_571_ = v_reuseFailAlloc_595_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
uint8_t v___x_572_; lean_object* v___x_573_; 
v___x_572_ = 0;
v___x_573_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_a_567_, v___x_571_, v___f_569_, v___x_572_, v___x_572_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_nat_add(v_val_551_, v___x_516_);
lean_dec(v_val_551_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_576_);
v___x_578_ = v___x_557_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_upperBound_535_);
v___x_578_ = v_reuseFailAlloc_586_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; size_t v___x_583_; size_t v___x_584_; 
v___x_579_ = lean_array_push(v_fst_483_, v_a_574_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_539_);
lean_ctor_set(v___x_580_, 1, v___x_519_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_578_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_579_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_469_, v___x_583_);
v_i_469_ = v___x_584_;
v_b_470_ = v___x_582_;
goto _start;
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_del_object(v___x_557_);
lean_dec(v_val_551_);
lean_dec_ref(v___x_539_);
lean_dec(v_upperBound_535_);
lean_dec_ref(v___x_519_);
lean_dec(v_fst_483_);
lean_dec_ref(v_fixedArgs_466_);
v_a_587_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_573_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_573_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_ref_559_);
lean_del_object(v___x_557_);
lean_del_object(v___x_553_);
lean_dec(v_val_551_);
lean_dec_ref(v___x_539_);
lean_dec(v___x_536_);
lean_dec(v_upperBound_535_);
lean_dec_ref(v___x_519_);
lean_dec(v_fst_483_);
lean_dec_ref(v_fixedArgs_466_);
v_a_596_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_566_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_566_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_ref_559_);
lean_del_object(v___x_557_);
lean_del_object(v___x_553_);
lean_dec(v_val_551_);
lean_dec_ref(v___x_539_);
lean_dec(v___x_536_);
lean_dec(v_upperBound_535_);
lean_dec_ref(v___x_519_);
lean_dec(v_fst_483_);
lean_dec_ref(v_fixedArgs_466_);
v_a_604_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_561_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_561_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
v___jp_540_:
{
lean_object* v___x_542_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_519_);
lean_ctor_set(v___x_493_, 0, v___x_539_);
v___x_542_ = v___x_493_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_519_);
v___x_542_ = v_reuseFailAlloc_550_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_542_);
v___x_544_ = v___x_489_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_549_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_544_);
v___x_546_ = v___x_485_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object* v_fixedParamPerms_632_, lean_object* v_fixedArgs_633_, lean_object* v_as_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_646_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_632_, v_fixedArgs_633_, v_as_634_, v_sz_boxed_645_, v_i_boxed_646_, v_b_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v_as_634_);
lean_dec_ref(v_fixedParamPerms_632_);
return v_res_647_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object* v_upperBound_660_, lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v_termMeasures_663_, lean_object* v_names_664_, lean_object* v_a_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_a_675_; uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v_a_665_, v_upperBound_660_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v_a_665_);
lean_dec_ref(v___x_662_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_b_666_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_array_fget_borrowed(v___x_661_, v_a_665_);
lean_inc(v___x_681_);
lean_inc_ref(v___x_662_);
v___x_682_ = l_Lean_Meta_isExprDefEqGuarded(v___x_662_, v___x_681_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_box(0);
v___x_685_ = lean_unbox(v_a_683_);
lean_dec(v_a_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_ref_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_686_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
v___x_687_ = lean_array_get_borrowed(v___x_686_, v_termMeasures_663_, v_a_665_);
v_ref_688_ = lean_ctor_get(v___x_687_, 0);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
v___x_691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
v___x_692_ = lean_box(0);
v___x_693_ = lean_array_get_borrowed(v___x_692_, v_names_664_, v___x_689_);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_MessageData_ofName(v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_691_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_690_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
lean_inc_ref(v___x_662_);
v___x_699_ = l_Lean_indentExpr(v___x_662_);
v___x_700_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_698_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
v___x_704_ = lean_array_get_borrowed(v___x_692_, v_names_664_, v_a_665_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_MessageData_ofName(v___x_704_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_703_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_696_);
lean_inc(v___x_681_);
v___x_708_ = l_Lean_indentExpr(v___x_681_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_700_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_702_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_688_, v___x_713_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
v_a_675_ = v___x_684_;
goto v___jp_674_;
}
else
{
lean_dec(v_a_665_);
lean_dec_ref(v___x_662_);
return v___x_714_;
}
}
else
{
v_a_675_ = v___x_684_;
goto v___jp_674_;
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_a_665_);
lean_dec_ref(v___x_662_);
v_a_715_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_682_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_682_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_a_665_, v___x_676_);
lean_dec(v_a_665_);
v_a_665_ = v___x_677_;
v_b_666_ = v_a_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object* v_upperBound_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_termMeasures_726_, lean_object* v_names_727_, lean_object* v_a_728_, lean_object* v_b_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_723_, v___x_724_, v___x_725_, v_termMeasures_726_, v_names_727_, v_a_728_, v_b_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v_names_727_);
lean_dec_ref(v_termMeasures_726_);
lean_dec_ref(v___x_724_);
lean_dec(v_upperBound_723_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* v_names_742_, lean_object* v_fixedParamPerms_743_, lean_object* v_fixedArgs_744_, lean_object* v_arities_745_, lean_object* v_termMeasures_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; lean_object* v_codomains_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; size_t v_sz_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v_codomains_755_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__0));
v___x_756_ = lean_array_get_size(v_names_742_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__1));
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
v___x_759_ = lean_array_get_size(v_arities_745_);
v___x_760_ = l_Array_toSubarray___redArg(v_arities_745_, v___x_754_, v___x_759_);
v___x_761_ = lean_array_get_size(v_termMeasures_746_);
lean_inc_ref(v_termMeasures_746_);
v___x_762_ = l_Array_toSubarray___redArg(v_termMeasures_746_, v___x_754_, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_760_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_758_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_codomains_755_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v_sz_766_ = lean_array_size(v_names_742_);
v___x_767_ = ((size_t)0ULL);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_743_, v_fixedArgs_744_, v_names_742_, v_sz_766_, v___x_767_, v___x_765_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_fst_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v_fst_770_ = lean_ctor_get(v_a_769_, 0);
lean_inc(v_fst_770_);
lean_dec(v_a_769_);
v___x_771_ = l_Lean_instInhabitedExpr;
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_array_get_size(v_fst_770_);
v___x_774_ = lean_array_get(v___x_771_, v_fst_770_, v___x_754_);
v___x_775_ = lean_box(0);
lean_inc(v___x_774_);
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v___x_773_, v_fst_770_, v___x_774_, v_termMeasures_746_, v_names_742_, v___x_772_, v___x_775_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec_ref(v_termMeasures_746_);
lean_dec(v_fst_770_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_776_, 0);
lean_dec(v_unused_784_);
v___x_778_ = v___x_776_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_dec(v___x_776_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_774_);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_774_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v___x_774_);
v_a_785_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_776_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_776_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_termMeasures_746_);
v_a_793_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_768_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_768_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* v_names_801_, lean_object* v_fixedParamPerms_802_, lean_object* v_fixedArgs_803_, lean_object* v_arities_804_, lean_object* v_termMeasures_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_WF_checkCodomains(v_names_801_, v_fixedParamPerms_802_, v_fixedArgs_803_, v_arities_804_, v_termMeasures_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_fixedParamPerms_802_);
lean_dec_ref(v_names_801_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object* v_00_u03b1_814_, lean_object* v_ref_815_, lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_815_, v_msg_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object* v_00_u03b1_825_, lean_object* v_ref_826_, lean_object* v_msg_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(v_00_u03b1_825_, v_ref_826_, v_msg_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_ref_826_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object* v_upperBound_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_termMeasures_839_, lean_object* v_names_840_, lean_object* v_inst_841_, lean_object* v_R_842_, lean_object* v_a_843_, lean_object* v_b_844_, lean_object* v_c_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_836_, v___x_837_, v___x_838_, v_termMeasures_839_, v_names_840_, v_a_843_, v_b_844_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_854_ = _args[0];
lean_object* v___x_855_ = _args[1];
lean_object* v___x_856_ = _args[2];
lean_object* v_termMeasures_857_ = _args[3];
lean_object* v_names_858_ = _args[4];
lean_object* v_inst_859_ = _args[5];
lean_object* v_R_860_ = _args[6];
lean_object* v_a_861_ = _args[7];
lean_object* v_b_862_ = _args[8];
lean_object* v_c_863_ = _args[9];
lean_object* v___y_864_ = _args[10];
lean_object* v___y_865_ = _args[11];
lean_object* v___y_866_ = _args[12];
lean_object* v___y_867_ = _args[13];
lean_object* v___y_868_ = _args[14];
lean_object* v___y_869_ = _args[15];
lean_object* v___y_870_ = _args[16];
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(v_upperBound_854_, v___x_855_, v___x_856_, v_termMeasures_857_, v_names_858_, v_inst_859_, v_R_860_, v_a_861_, v_b_862_, v_c_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_names_858_);
lean_dec_ref(v_termMeasures_857_);
lean_dec_ref(v___x_855_);
lean_dec(v_upperBound_854_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object* v_00_u03b1_872_, lean_object* v_msg_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object* v_00_u03b1_882_, lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(v_00_u03b1_882_, v_msg_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object* v_msgData_892_, lean_object* v_macroStack_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_892_, v_macroStack_893_, v___y_898_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_902_, lean_object* v_macroStack_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_902_, v_macroStack_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object* v_e_912_, lean_object* v___y_913_){
_start:
{
uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_915_ = l_Lean_Expr_hasMVar(v_e_912_);
v___x_916_ = lean_bool_not(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v___x_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_922_; lean_object* v_cache_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
v___x_917_ = lean_st_ref_get(v___y_913_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_mctx_918_);
lean_dec(v___x_917_);
v___x_919_ = l_Lean_instantiateMVarsCore(v_mctx_918_, v_e_912_);
v_fst_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v___x_919_, 1);
lean_inc(v_snd_921_);
lean_dec_ref(v___x_919_);
v___x_922_ = lean_st_ref_take(v___y_913_);
v_cache_923_ = lean_ctor_get(v___x_922_, 1);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_922_, 2);
v_postponed_925_ = lean_ctor_get(v___x_922_, 3);
v_diag_926_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_936_);
v___x_928_ = v___x_922_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_diag_926_);
lean_inc(v_postponed_925_);
lean_inc(v_zetaDeltaFVarIds_924_);
lean_inc(v_cache_923_);
lean_dec(v___x_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_snd_921_);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_snd_921_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_cache_923_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_diag_926_);
v___x_931_ = v_reuseFailAlloc_934_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_st_ref_set(v___y_913_, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_fst_920_);
return v___x_933_;
}
}
}
else
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_e_912_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_938_, v___y_939_);
lean_dec(v___y_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object* v_e_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_942_, v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object* v_e_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(v_e_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object* v_fixedParamPerms_960_, lean_object* v_fixedArgs_961_, size_t v_sz_962_, size_t v_i_963_, lean_object* v_bs_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v_fixedArgs_961_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_bs_964_);
return v___x_971_;
}
else
{
lean_object* v_v_972_; lean_object* v_perms_973_; lean_object* v_fn_974_; lean_object* v___x_975_; lean_object* v_bs_x27_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_v_972_ = lean_array_uget_borrowed(v_bs_964_, v_i_963_);
v_perms_973_ = lean_ctor_get(v_fixedParamPerms_960_, 1);
v_fn_974_ = lean_ctor_get(v_v_972_, 1);
lean_inc_ref(v_fn_974_);
v___x_975_ = lean_unsigned_to_nat(0u);
v_bs_x27_976_ = lean_array_uset(v_bs_964_, v_i_963_, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_978_ = lean_usize_to_nat(v_i_963_);
v___x_979_ = lean_array_get_borrowed(v___x_977_, v_perms_973_, v___x_978_);
lean_dec(v___x_978_);
lean_inc_ref(v_fixedArgs_961_);
lean_inc(v___x_979_);
v___x_980_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_979_, v_fn_974_, v_fixedArgs_961_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_963_, v___x_982_);
v___x_984_ = lean_array_uset(v_bs_x27_976_, v_i_963_, v_a_981_);
v_i_963_ = v___x_983_;
v_bs_964_ = v___x_984_;
goto _start;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_bs_x27_976_);
lean_dec_ref(v_fixedArgs_961_);
v_a_986_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_980_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_980_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object* v_fixedParamPerms_994_, lean_object* v_fixedArgs_995_, lean_object* v_sz_996_, lean_object* v_i_997_, lean_object* v_bs_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_996_);
lean_dec(v_sz_996_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_994_, v_fixedArgs_995_, v_sz_boxed_1004_, v_i_boxed_1005_, v_bs_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v_fixedParamPerms_994_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object* v_argType_1013_, lean_object* v_argsPacker_1014_, lean_object* v_declNames_1015_, lean_object* v_fixedParamPerms_1016_, lean_object* v_fixedArgs_1017_, lean_object* v_termMeasures_1018_, lean_object* v_k_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
lean_inc_ref(v_argType_1013_);
v___x_1027_ = l_Lean_Meta_getLevel(v_argType_1013_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc_ref(v_argsPacker_1014_);
v___x_1029_ = l_Lean_Meta_ArgsPacker_arities(v_argsPacker_1014_);
lean_inc_ref(v_termMeasures_1018_);
lean_inc_ref(v_fixedArgs_1017_);
v___x_1030_ = l_Lean_Elab_WF_checkCodomains(v_declNames_1015_, v_fixedParamPerms_1016_, v_fixedArgs_1017_, v___x_1029_, v_termMeasures_1018_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_n(v_a_1031_, 2);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = l_Lean_Meta_getLevel(v_a_1031_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v_sz_1034_ = lean_array_size(v_termMeasures_1018_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1016_, v_fixedArgs_1017_, v_sz_1034_, v___x_1035_, v_termMeasures_1018_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_1014_, v_a_1037_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v_a_1037_);
lean_dec_ref(v_argsPacker_1014_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1));
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_a_1033_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
lean_inc_ref(v___x_1042_);
v___x_1043_ = l_Lean_Expr_const___override(v___x_1040_, v___x_1042_);
lean_inc(v_a_1031_);
v___x_1044_ = l_Lean_Expr_app___override(v___x_1043_, v_a_1031_);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_Meta_synthInstance(v___x_1044_, v___x_1045_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3));
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_a_1028_);
lean_ctor_set(v___x_1049_, 1, v___x_1042_);
v___x_1050_ = l_Lean_Expr_const___override(v___x_1048_, v___x_1049_);
v___x_1051_ = l_Lean_mkApp4(v___x_1050_, v_argType_1013_, v_a_1031_, v_a_1039_, v_a_1047_);
v___x_1052_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v___x_1051_, v___y_1023_);
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = lean_apply_8(v_k_1019_, v_a_1053_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, lean_box(0));
return v___x_1054_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref_known(v___x_1042_, 2);
lean_dec(v_a_1039_);
lean_dec(v_a_1031_);
lean_dec(v_a_1028_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_argType_1013_);
v_a_1055_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1046_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1046_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_1033_);
lean_dec(v_a_1031_);
lean_dec(v_a_1028_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_argType_1013_);
v_a_1063_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1038_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1038_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_1033_);
lean_dec(v_a_1031_);
lean_dec(v_a_1028_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_argsPacker_1014_);
lean_dec_ref(v_argType_1013_);
v_a_1071_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1036_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1036_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1031_);
lean_dec(v_a_1028_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_termMeasures_1018_);
lean_dec_ref(v_fixedArgs_1017_);
lean_dec_ref(v_argsPacker_1014_);
lean_dec_ref(v_argType_1013_);
v_a_1079_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1032_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1032_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1028_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_termMeasures_1018_);
lean_dec_ref(v_fixedArgs_1017_);
lean_dec_ref(v_argsPacker_1014_);
lean_dec_ref(v_argType_1013_);
v_a_1087_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1030_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1030_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_k_1019_);
lean_dec_ref(v_termMeasures_1018_);
lean_dec_ref(v_fixedArgs_1017_);
lean_dec_ref(v_argsPacker_1014_);
lean_dec_ref(v_argType_1013_);
v_a_1095_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1027_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1027_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object* v_argType_1103_, lean_object* v_argsPacker_1104_, lean_object* v_declNames_1105_, lean_object* v_fixedParamPerms_1106_, lean_object* v_fixedArgs_1107_, lean_object* v_termMeasures_1108_, lean_object* v_k_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(v_argType_1103_, v_argsPacker_1104_, v_declNames_1105_, v_fixedParamPerms_1106_, v_fixedArgs_1107_, v_termMeasures_1108_, v_k_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec_ref(v_fixedParamPerms_1106_);
lean_dec_ref(v_declNames_1105_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object* v_declNames_1118_, lean_object* v_unaryPreDefName_1119_, lean_object* v_fixedParamPerms_1120_, lean_object* v_fixedArgs_1121_, lean_object* v_argsPacker_1122_, lean_object* v_argType_1123_, lean_object* v_termMeasures_1124_, lean_object* v_k_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1133_, 0, v_argType_1123_);
lean_closure_set(v___f_1133_, 1, v_argsPacker_1122_);
lean_closure_set(v___f_1133_, 2, v_declNames_1118_);
lean_closure_set(v___f_1133_, 3, v_fixedParamPerms_1120_);
lean_closure_set(v___f_1133_, 4, v_fixedArgs_1121_);
lean_closure_set(v___f_1133_, 5, v_termMeasures_1124_);
lean_closure_set(v___f_1133_, 6, v_k_1125_);
v___x_1134_ = l_Lean_Elab_Term_withDeclName___redArg(v_unaryPreDefName_1119_, v___f_1133_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object* v_declNames_1135_, lean_object* v_unaryPreDefName_1136_, lean_object* v_fixedParamPerms_1137_, lean_object* v_fixedArgs_1138_, lean_object* v_argsPacker_1139_, lean_object* v_argType_1140_, lean_object* v_termMeasures_1141_, lean_object* v_k_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1135_, v_unaryPreDefName_1136_, v_fixedParamPerms_1137_, v_fixedArgs_1138_, v_argsPacker_1139_, v_argType_1140_, v_termMeasures_1141_, v_k_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* v_00_u03b1_1151_, lean_object* v_declNames_1152_, lean_object* v_unaryPreDefName_1153_, lean_object* v_fixedParamPerms_1154_, lean_object* v_fixedArgs_1155_, lean_object* v_argsPacker_1156_, lean_object* v_argType_1157_, lean_object* v_termMeasures_1158_, lean_object* v_k_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1152_, v_unaryPreDefName_1153_, v_fixedParamPerms_1154_, v_fixedArgs_1155_, v_argsPacker_1156_, v_argType_1157_, v_termMeasures_1158_, v_k_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_declNames_1169_, lean_object* v_unaryPreDefName_1170_, lean_object* v_fixedParamPerms_1171_, lean_object* v_fixedArgs_1172_, lean_object* v_argsPacker_1173_, lean_object* v_argType_1174_, lean_object* v_termMeasures_1175_, lean_object* v_k_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_WF_elabWFRel(v_00_u03b1_1168_, v_declNames_1169_, v_unaryPreDefName_1170_, v_fixedParamPerms_1171_, v_fixedArgs_1172_, v_argsPacker_1173_, v_argType_1174_, v_termMeasures_1175_, v_k_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object* v_fixedParamPerms_1185_, lean_object* v_fixedArgs_1186_, lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_bs_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1185_, v_fixedArgs_1186_, v_sz_1188_, v_i_1189_, v_bs_1190_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object* v_fixedParamPerms_1199_, lean_object* v_fixedArgs_1200_, lean_object* v_as_1201_, lean_object* v_sz_1202_, lean_object* v_i_1203_, lean_object* v_bs_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
size_t v_sz_boxed_1212_; size_t v_i_boxed_1213_; lean_object* v_res_1214_; 
v_sz_boxed_1212_ = lean_unbox_usize(v_sz_1202_);
lean_dec(v_sz_1202_);
v_i_boxed_1213_ = lean_unbox_usize(v_i_1203_);
lean_dec(v_i_1203_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(v_fixedParamPerms_1199_, v_fixedArgs_1200_, v_as_1201_, v_sz_boxed_1212_, v_i_boxed_1213_, v_bs_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_as_1201_);
lean_dec_ref(v_fixedParamPerms_1199_);
return v_res_1214_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
}
#ifdef __cplusplus
}
#endif
