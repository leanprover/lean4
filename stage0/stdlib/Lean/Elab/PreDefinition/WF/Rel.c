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
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_6145__overap_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0, &l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0);
v___x_6145__overap_11_ = lean_panic_fn_borrowed(v___x_10_, v_msg_2_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_12_ = lean_apply_7(v___x_6145__overap_11_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v___y_8_ = stack[6].m_obj;
lean_object* v_res_13_;
v_res_13_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v_msg_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_22_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(lean_object* v_k_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v_b_26_, lean_object* v_c_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; 
lean_inc(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
lean_inc(v___y_25_);
lean_inc_ref(v___y_24_);
v___x_33_ = lean_apply_9(v_k_23_, v_b_26_, v_c_27_, v___y_24_, v___y_25_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_23_ = stack[0].m_obj;
lean_object* v___y_24_ = stack[1].m_obj;
lean_object* v___y_25_ = stack[2].m_obj;
lean_object* v_b_26_ = stack[3].m_obj;
lean_object* v_c_27_ = stack[4].m_obj;
lean_object* v___y_28_ = stack[5].m_obj;
lean_object* v___y_29_ = stack[6].m_obj;
lean_object* v___y_30_ = stack[7].m_obj;
lean_object* v___y_31_ = stack[8].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(v_k_23_, v___y_24_, v___y_25_, v_b_26_, v_c_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(lean_object* v_k_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v_b_38_, lean_object* v_c_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(v_k_35_, v___y_36_, v___y_37_, v_b_38_, v_c_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(lean_object* v_type_46_, lean_object* v_maxFVars_x3f_47_, lean_object* v_k_48_, uint8_t v_cleanupAnnotations_49_, uint8_t v_whnfType_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; 
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___f_58_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_58_, 0, v_k_48_);
lean_closure_set(v___f_58_, 1, v___y_51_);
lean_closure_set(v___f_58_, 2, v___y_52_);
v___x_59_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_46_, v_maxFVars_x3f_47_, v___f_58_, v_cleanupAnnotations_49_, v_whnfType_50_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
if (lean_obj_tag(v___x_59_) == 0)
{
return v___x_59_;
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_46_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_47_ = stack[1].m_obj;
lean_object* v_k_48_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_49_ = stack[3].m_num;
uint8_t v_whnfType_50_ = stack[4].m_num;
lean_object* v___y_51_ = stack[5].m_obj;
lean_object* v___y_52_ = stack[6].m_obj;
lean_object* v___y_53_ = stack[7].m_obj;
lean_object* v___y_54_ = stack[8].m_obj;
lean_object* v___y_55_ = stack[9].m_obj;
lean_object* v___y_56_ = stack[10].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_type_46_, v_maxFVars_x3f_47_, v_k_48_, v_cleanupAnnotations_49_, v_whnfType_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(lean_object* v_type_69_, lean_object* v_maxFVars_x3f_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_81_; uint8_t v_whnfType_boxed_82_; lean_object* v_res_83_; 
v_cleanupAnnotations_boxed_81_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_82_ = lean_unbox(v_whnfType_73_);
v_res_83_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_type_69_, v_maxFVars_x3f_70_, v_k_71_, v_cleanupAnnotations_boxed_81_, v_whnfType_boxed_82_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_object* v_00_u03b1_84_, lean_object* v_type_85_, lean_object* v_maxFVars_x3f_86_, lean_object* v_k_87_, uint8_t v_cleanupAnnotations_88_, uint8_t v_whnfType_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_type_85_, v_maxFVars_x3f_86_, v_k_87_, v_cleanupAnnotations_88_, v_whnfType_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_85_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_86_ = stack[2].m_obj;
lean_object* v_k_87_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_88_ = stack[4].m_num;
uint8_t v_whnfType_89_ = stack[5].m_num;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v___y_94_ = stack[10].m_obj;
lean_object* v___y_95_ = stack[11].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_box(0), v_type_85_, v_maxFVars_x3f_86_, v_k_87_, v_cleanupAnnotations_88_, v_whnfType_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(lean_object* v_00_u03b1_99_, lean_object* v_type_100_, lean_object* v_maxFVars_x3f_101_, lean_object* v_k_102_, lean_object* v_cleanupAnnotations_103_, lean_object* v_whnfType_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_112_; uint8_t v_whnfType_boxed_113_; lean_object* v_res_114_; 
v_cleanupAnnotations_boxed_112_ = lean_unbox(v_cleanupAnnotations_103_);
v_whnfType_boxed_113_ = lean_unbox(v_whnfType_104_);
v_res_114_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(v_00_u03b1_99_, v_type_100_, v_maxFVars_x3f_101_, v_k_102_, v_cleanupAnnotations_boxed_112_, v_whnfType_boxed_113_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_114_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(lean_object* v_a_115_, lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
v___x_121_ = l_Lean_instBEqFVarId_beq(v_a_115_, v___x_120_);
if (v___x_121_ == 0)
{
size_t v___x_122_; size_t v___x_123_; 
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_117_, v___x_122_);
v_i_117_ = v___x_123_;
goto _start;
}
else
{
return v___x_121_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_115_ = stack[0].m_obj;
lean_object* v_as_116_ = stack[1].m_obj;
size_t v_i_117_ = stack[2].m_num;
size_t v_stop_118_ = stack[3].m_num;
uint8_t v_res_126_;
v_res_126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_115_, v_as_116_, v_i_117_, v_stop_118_);
stack->m_num = v_res_126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(lean_object* v_a_127_, lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_stop_130_){
_start:
{
size_t v_i_boxed_131_; size_t v_stop_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_i_boxed_131_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_130_);
lean_dec(v_stop_130_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_127_, v_as_128_, v_i_boxed_131_, v_stop_boxed_132_);
lean_dec_ref(v_as_128_);
lean_dec(v_a_127_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(lean_object* v_as_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_as_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
size_t v___x_140_; size_t v___x_141_; uint8_t v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_138_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_136_, v_as_135_, v___x_140_, v___x_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_135_ = stack[0].m_obj;
lean_object* v_a_136_ = stack[1].m_obj;
uint8_t v_res_143_;
v_res_143_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v_as_135_, v_a_136_);
stack->m_num = v_res_143_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(lean_object* v_as_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v_as_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_as_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(lean_object* v___x_148_, lean_object* v_e_149_){
_start:
{
uint8_t v___x_150_; lean_object* v_d_152_; lean_object* v_b_153_; 
v___x_150_ = l_Lean_Expr_hasFVar(v_e_149_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
switch(lean_obj_tag(v_e_149_))
{
case 7:
{
lean_object* v_binderType_156_; lean_object* v_body_157_; 
v_binderType_156_ = lean_ctor_get(v_e_149_, 1);
v_body_157_ = lean_ctor_get(v_e_149_, 2);
v_d_152_ = v_binderType_156_;
v_b_153_ = v_body_157_;
goto v___jp_151_;
}
case 6:
{
lean_object* v_binderType_158_; lean_object* v_body_159_; 
v_binderType_158_ = lean_ctor_get(v_e_149_, 1);
v_body_159_ = lean_ctor_get(v_e_149_, 2);
v_d_152_ = v_binderType_158_;
v_b_153_ = v_body_159_;
goto v___jp_151_;
}
case 10:
{
lean_object* v_expr_160_; 
v_expr_160_ = lean_ctor_get(v_e_149_, 1);
v_e_149_ = v_expr_160_;
goto _start;
}
case 8:
{
lean_object* v_type_162_; lean_object* v_value_163_; lean_object* v_body_164_; uint8_t v___x_165_; 
v_type_162_ = lean_ctor_get(v_e_149_, 1);
v_value_163_ = lean_ctor_get(v_e_149_, 2);
v_body_164_ = lean_ctor_get(v_e_149_, 3);
v___x_165_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_148_, v_type_162_);
if (v___x_165_ == 0)
{
uint8_t v___x_166_; 
v___x_166_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_148_, v_value_163_);
if (v___x_166_ == 0)
{
v_e_149_ = v_body_164_;
goto _start;
}
else
{
return v___x_150_;
}
}
else
{
return v___x_150_;
}
}
case 5:
{
lean_object* v_fn_168_; lean_object* v_arg_169_; uint8_t v___x_170_; 
v_fn_168_ = lean_ctor_get(v_e_149_, 0);
v_arg_169_ = lean_ctor_get(v_e_149_, 1);
v___x_170_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_148_, v_fn_168_);
if (v___x_170_ == 0)
{
v_e_149_ = v_arg_169_;
goto _start;
}
else
{
return v___x_150_;
}
}
case 11:
{
lean_object* v_struct_172_; 
v_struct_172_ = lean_ctor_get(v_e_149_, 2);
v_e_149_ = v_struct_172_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_174_; uint8_t v___x_175_; 
v_fvarId_174_ = lean_ctor_get(v_e_149_, 0);
v___x_175_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v___x_148_, v_fvarId_174_);
return v___x_175_;
}
default: 
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
}
}
v___jp_151_:
{
uint8_t v___x_154_; 
v___x_154_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_148_, v_d_152_);
if (v___x_154_ == 0)
{
v_e_149_ = v_b_153_;
goto _start;
}
else
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_148_ = stack[0].m_obj;
lean_object* v_e_149_ = stack[1].m_obj;
uint8_t v_res_177_;
v_res_177_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_148_, v_e_149_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object* v___x_178_, lean_object* v_e_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_178_, v_e_179_);
lean_dec_ref(v_e_179_);
lean_dec_ref(v___x_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t v_sz_182_, size_t v_i_183_, lean_object* v_bs_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_usize_dec_lt(v_i_183_, v_sz_182_);
if (v___x_185_ == 0)
{
return v_bs_184_;
}
else
{
lean_object* v_v_186_; lean_object* v___x_187_; lean_object* v_bs_x27_188_; lean_object* v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v_v_186_ = lean_array_uget(v_bs_184_, v_i_183_);
v___x_187_ = lean_unsigned_to_nat(0u);
v_bs_x27_188_ = lean_array_uset(v_bs_184_, v_i_183_, v___x_187_);
v___x_189_ = l_Lean_Expr_fvarId_x21(v_v_186_);
lean_dec(v_v_186_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_183_, v___x_190_);
v___x_192_ = lean_array_uset(v_bs_x27_188_, v_i_183_, v___x_189_);
v_i_183_ = v___x_191_;
v_bs_184_ = v___x_192_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_182_ = stack[0].m_num;
size_t v_i_183_ = stack[1].m_num;
lean_object* v_bs_184_ = stack[2].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_182_, v_i_183_, v_bs_184_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object* v_sz_195_, lean_object* v_i_196_, lean_object* v_bs_197_){
_start:
{
size_t v_sz_boxed_198_; size_t v_i_boxed_199_; lean_object* v_res_200_; 
v_sz_boxed_198_ = lean_unbox_usize(v_sz_195_);
lean_dec(v_sz_195_);
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_boxed_198_, v_i_boxed_199_, v_bs_197_);
return v_res_200_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object* v_msgData_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_env_208_; uint8_t v___x_209_; lean_object* v_env_210_; lean_object* v___x_211_; lean_object* v_toCold_212_; lean_object* v_mctx_213_; lean_object* v_lctx_214_; lean_object* v_options_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_207_ = lean_st_ref_get(v___y_205_);
v_env_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_207_);
v___x_209_ = 0;
v_env_210_ = l_Lean_Environment_setRecordingDeps(v_env_208_, v___x_209_);
v___x_211_ = lean_st_ref_get(v___y_203_);
v_toCold_212_ = lean_ctor_get(v___y_204_, 0);
v_mctx_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_213_);
lean_dec(v___x_211_);
v_lctx_214_ = lean_ctor_get(v___y_202_, 2);
v_options_215_ = lean_ctor_get(v_toCold_212_, 2);
lean_inc_ref(v_options_215_);
lean_inc_ref(v_lctx_214_);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v_env_210_);
lean_ctor_set(v___x_216_, 1, v_mctx_213_);
lean_ctor_set(v___x_216_, 2, v_lctx_214_);
lean_ctor_set(v___x_216_, 3, v_options_215_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_msgData_201_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_201_ = stack[0].m_obj;
lean_object* v___y_202_ = stack[1].m_obj;
lean_object* v___y_203_ = stack[2].m_obj;
lean_object* v___y_204_ = stack[3].m_obj;
lean_object* v___y_205_ = stack[4].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object* v_msgData_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object* v_opts_227_, lean_object* v_opt_228_){
_start:
{
lean_object* v_name_229_; lean_object* v_defValue_230_; lean_object* v_map_231_; lean_object* v___x_232_; 
v_name_229_ = lean_ctor_get(v_opt_228_, 0);
v_defValue_230_ = lean_ctor_get(v_opt_228_, 1);
v_map_231_ = lean_ctor_get(v_opts_227_, 0);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_231_, v_name_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
uint8_t v___x_233_; 
v___x_233_ = lean_unbox(v_defValue_230_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
if (lean_obj_tag(v_val_234_) == 1)
{
uint8_t v_v_235_; 
v_v_235_ = lean_ctor_get_uint8(v_val_234_, 0);
lean_dec_ref_known(v_val_234_, 0);
return v_v_235_;
}
else
{
uint8_t v___x_236_; 
lean_dec(v_val_234_);
v___x_236_ = lean_unbox(v_defValue_230_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_227_ = stack[0].m_obj;
lean_object* v_opt_228_ = stack[1].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_227_, v_opt_228_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_238_, v_opt_239_);
lean_dec_ref(v_opt_239_);
lean_dec_ref(v_opts_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_box(1);
v___x_243_ = l_Lean_MessageData_ofFormat(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2));
v___x_248_ = l_Lean_MessageData_ofFormat(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
return v_x_249_;
}
else
{
lean_object* v_head_251_; lean_object* v_tail_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_274_; 
v_head_251_ = lean_ctor_get(v_x_250_, 0);
v_tail_252_ = lean_ctor_get(v_x_250_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_274_ == 0)
{
v___x_254_ = v_x_250_;
v_isShared_255_ = v_isSharedCheck_274_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_tail_252_);
lean_inc(v_head_251_);
lean_dec(v_x_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_274_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_before_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_272_; 
v_before_256_ = lean_ctor_get(v_head_251_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_head_251_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_head_251_, 1);
lean_dec(v_unused_273_);
v___x_258_ = v_head_251_;
v_isShared_259_ = v_isSharedCheck_272_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_before_256_);
lean_dec(v_head_251_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_272_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 7);
lean_ctor_set(v___x_258_, 1, v___x_260_);
lean_ctor_set(v___x_258_, 0, v_x_249_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_x_249_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_271_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 7);
lean_ctor_set(v___x_254_, 1, v___x_263_);
lean_ctor_set(v___x_254_, 0, v___x_262_);
v___x_265_ = v___x_254_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_270_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = l_Lean_MessageData_ofSyntax(v_before_256_);
v___x_267_ = l_Lean_indentD(v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v_x_249_ = v___x_268_;
v_x_250_ = v_tail_252_;
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
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1));
v___x_279_ = l_Lean_MessageData_ofFormat(v___x_278_);
return v___x_279_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object* v_msgData_280_, lean_object* v_macroStack_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_282_);
v___x_285_ = l_Lean_Elab_pp_macroStack;
v___x_286_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v___x_284_, v___x_285_);
lean_dec_ref(v___x_284_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec(v_macroStack_281_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_msgData_280_);
return v___x_287_;
}
else
{
if (lean_obj_tag(v_macroStack_281_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v_msgData_280_);
return v___x_288_;
}
else
{
lean_object* v_head_289_; lean_object* v_after_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_305_; 
v_head_289_ = lean_ctor_get(v_macroStack_281_, 0);
lean_inc(v_head_289_);
v_after_290_ = lean_ctor_get(v_head_289_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_head_289_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_head_289_, 0);
lean_dec(v_unused_306_);
v___x_292_ = v_head_289_;
v_isShared_293_ = v_isSharedCheck_305_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_after_290_);
lean_dec(v_head_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_305_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 7);
lean_ctor_set(v___x_292_, 1, v___x_294_);
lean_ctor_set(v___x_292_, 0, v_msgData_280_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_msgData_280_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_304_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_msgData_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_297_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_MessageData_ofSyntax(v_after_290_);
v___x_300_ = l_Lean_indentD(v___x_299_);
v_msgData_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_301_, 0, v___x_298_);
lean_ctor_set(v_msgData_301_, 1, v___x_300_);
v___x_302_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(v_msgData_301_, v_macroStack_281_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_280_ = stack[0].m_obj;
lean_object* v_macroStack_281_ = stack[1].m_obj;
lean_object* v___y_282_ = stack[2].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_280_, v_macroStack_281_, v___y_282_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_308_, lean_object* v_macroStack_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_308_, v_macroStack_309_, v___y_310_);
lean_dec_ref(v___y_310_);
return v_res_312_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_ref_321_; lean_object* v_macroStack_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_ref_321_ = lean_ctor_get(v___y_318_, 2);
v_macroStack_322_ = lean_ctor_get(v___y_314_, 1);
v___x_323_ = l_Lean_Elab_getBetterRef(v_ref_321_, v_macroStack_322_);
v___x_324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msg_313_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v___x_324_);
lean_inc(v_macroStack_322_);
v___x_326_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_a_325_, v_macroStack_322_, v___y_318_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_323_);
lean_ctor_set(v___x_331_, 1, v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 1);
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_313_ = stack[0].m_obj;
lean_object* v___y_314_ = stack[1].m_obj;
lean_object* v___y_315_ = stack[2].m_obj;
lean_object* v___y_316_ = stack[3].m_obj;
lean_object* v___y_317_ = stack[4].m_obj;
lean_object* v___y_318_ = stack[5].m_obj;
lean_object* v___y_319_ = stack[6].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_345_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object* v_ref_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_toCold_355_; lean_object* v_currRecDepth_356_; lean_object* v_ref_357_; uint16_t v_optionFlags_358_; uint8_t v_suppressElabErrors_359_; uint8_t v_isRecordingDeps_360_; lean_object* v_ref_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_toCold_355_ = lean_ctor_get(v___y_352_, 0);
v_currRecDepth_356_ = lean_ctor_get(v___y_352_, 1);
v_ref_357_ = lean_ctor_get(v___y_352_, 2);
v_optionFlags_358_ = lean_ctor_get_uint16(v___y_352_, sizeof(void*)*3);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 2);
v_isRecordingDeps_360_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 3);
v_ref_361_ = l_Lean_replaceRef(v_ref_346_, v_ref_357_);
lean_inc(v_currRecDepth_356_);
lean_inc_ref(v_toCold_355_);
v___x_362_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_362_, 0, v_toCold_355_);
lean_ctor_set(v___x_362_, 1, v_currRecDepth_356_);
lean_ctor_set(v___x_362_, 2, v_ref_361_);
lean_ctor_set_uint16(v___x_362_, sizeof(void*)*3, v_optionFlags_358_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3 + 2, v_suppressElabErrors_359_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3 + 3, v_isRecordingDeps_360_);
v___x_363_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___x_362_, v___y_353_);
lean_dec_ref_known(v___x_362_, 3);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_346_ = stack[0].m_obj;
lean_object* v_msg_347_ = stack[1].m_obj;
lean_object* v___y_348_ = stack[2].m_obj;
lean_object* v___y_349_ = stack[3].m_obj;
lean_object* v___y_350_ = stack[4].m_obj;
lean_object* v___y_351_ = stack[5].m_obj;
lean_object* v___y_352_ = stack[6].m_obj;
lean_object* v___y_353_ = stack[7].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_346_, v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object* v_ref_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_365_, v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_ref_365_);
return v_res_374_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2));
v___x_379_ = lean_unsigned_to_nat(6u);
v___x_380_ = lean_unsigned_to_nat(33u);
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1));
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0));
v___x_383_ = l_mkPanicMessageWithDecl(v___x_382_, v___x_381_, v___x_380_, v___x_379_, v___x_378_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13));
v___x_400_ = l_Lean_MessageData_ofFormat(v___x_399_);
return v___x_400_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object* v___x_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_ref_404_, lean_object* v_xs_405_, lean_object* v_codomain_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_xs_405_);
v___x_415_ = lean_nat_dec_eq(v___x_414_, v___x_401_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v_codomain_406_);
lean_dec_ref(v_xs_405_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
v___x_416_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
v___x_417_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v___x_416_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
return v___x_417_;
}
else
{
size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_sz_418_ = lean_array_size(v_xs_405_);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_418_, v___x_419_, v_xs_405_);
v___x_421_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_420_, v_codomain_406_);
lean_dec_ref(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_codomain_406_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_423_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
v___x_424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
v___x_425_ = l_Lean_MessageData_ofName(v_a_402_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_indentExpr(v_a_403_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_423_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_404_, v___x_435_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v___x_436_, 0);
lean_dec(v_unused_444_);
v___x_438_ = v___x_436_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_dec(v___x_436_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_codomain_406_);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_codomain_406_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v_codomain_406_);
v_a_445_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_436_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_436_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_401_ = stack[0].m_obj;
lean_object* v_a_402_ = stack[1].m_obj;
lean_object* v_a_403_ = stack[2].m_obj;
lean_object* v_ref_404_ = stack[3].m_obj;
lean_object* v_xs_405_ = stack[4].m_obj;
lean_object* v_codomain_406_ = stack[5].m_obj;
lean_object* v___y_407_ = stack[6].m_obj;
lean_object* v___y_408_ = stack[7].m_obj;
lean_object* v___y_409_ = stack[8].m_obj;
lean_object* v___y_410_ = stack[9].m_obj;
lean_object* v___y_411_ = stack[10].m_obj;
lean_object* v___y_412_ = stack[11].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_401_, v_a_402_, v_a_403_, v_ref_404_, v_xs_405_, v_codomain_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object* v___x_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_ref_457_, lean_object* v_xs_458_, lean_object* v_codomain_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_454_, v_a_455_, v_a_456_, v_ref_457_, v_xs_458_, v_codomain_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_ref_457_);
lean_dec(v___x_454_);
return v_res_467_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Array_instInhabited___redArg();
return v___x_468_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object* v_fixedParamPerms_469_, lean_object* v_fixedArgs_470_, lean_object* v_as_471_, size_t v_sz_472_, size_t v_i_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_lt(v_i_473_, v_sz_472_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_fixedArgs_470_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_b_474_);
return v___x_483_;
}
else
{
lean_object* v_snd_484_; lean_object* v_snd_485_; lean_object* v_snd_486_; lean_object* v_fst_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_634_; 
v_snd_484_ = lean_ctor_get(v_b_474_, 1);
lean_inc(v_snd_484_);
v_snd_485_ = lean_ctor_get(v_snd_484_, 1);
lean_inc(v_snd_485_);
v_snd_486_ = lean_ctor_get(v_snd_485_, 1);
lean_inc(v_snd_486_);
v_fst_487_ = lean_ctor_get(v_b_474_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_b_474_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_b_474_, 1);
lean_dec(v_unused_635_);
v___x_489_ = v_b_474_;
v_isShared_490_ = v_isSharedCheck_634_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_fst_487_);
lean_dec(v_b_474_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_634_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_fst_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_632_; 
v_fst_491_ = lean_ctor_get(v_snd_484_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_snd_484_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_snd_484_, 1);
lean_dec(v_unused_633_);
v___x_493_ = v_snd_484_;
v_isShared_494_ = v_isSharedCheck_632_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_fst_491_);
lean_dec(v_snd_484_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_632_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_fst_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_630_; 
v_fst_495_ = lean_ctor_get(v_snd_485_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_snd_485_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_snd_485_, 1);
lean_dec(v_unused_631_);
v___x_497_ = v_snd_485_;
v_isShared_498_ = v_isSharedCheck_630_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_fst_495_);
lean_dec(v_snd_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_630_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_array_499_; lean_object* v_start_500_; lean_object* v_stop_501_; uint8_t v___x_502_; 
v_array_499_ = lean_ctor_get(v_snd_486_, 0);
v_start_500_ = lean_ctor_get(v_snd_486_, 1);
v_stop_501_ = lean_ctor_get(v_snd_486_, 2);
v___x_502_ = lean_nat_dec_lt(v_start_500_, v_stop_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_504_; 
lean_dec_ref(v_fixedArgs_470_);
if (v_isShared_498_ == 0)
{
v___x_504_ = v___x_497_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_fst_495_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_snd_486_);
v___x_504_ = v_reuseFailAlloc_512_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_504_);
v___x_506_ = v___x_493_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_511_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_506_);
v___x_508_ = v___x_489_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_626_; 
lean_inc(v_stop_501_);
lean_inc(v_start_500_);
lean_inc_ref(v_array_499_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_snd_486_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_627_ = lean_ctor_get(v_snd_486_, 2);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_snd_486_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_snd_486_, 0);
lean_dec(v_unused_629_);
v___x_514_ = v_snd_486_;
v_isShared_515_ = v_isSharedCheck_626_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_snd_486_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_626_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_array_516_; lean_object* v_start_517_; lean_object* v_stop_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v_array_516_ = lean_ctor_get(v_fst_495_, 0);
v_start_517_ = lean_ctor_get(v_fst_495_, 1);
v_stop_518_ = lean_ctor_get(v_fst_495_, 2);
v___x_519_ = lean_array_fget(v_array_499_, v_start_500_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_start_500_, v___x_520_);
lean_dec(v_start_500_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_521_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_array_499_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_stop_501_);
v___x_523_ = v_reuseFailAlloc_625_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v_start_517_, v_stop_518_);
if (v___x_524_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v___x_519_);
lean_dec_ref(v_fixedArgs_470_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_523_);
v___x_526_ = v___x_497_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_495_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_523_);
v___x_526_ = v_reuseFailAlloc_534_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_526_);
v___x_528_ = v___x_493_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_528_);
v___x_530_ = v___x_489_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_532_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_621_; 
lean_inc(v_stop_518_);
lean_inc(v_start_517_);
lean_inc_ref(v_array_516_);
v_isSharedCheck_621_ = !lean_is_exclusive(v_fst_495_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_622_ = lean_ctor_get(v_fst_495_, 2);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_fst_495_, 1);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_fst_495_, 0);
lean_dec(v_unused_624_);
v___x_536_ = v_fst_495_;
v_isShared_537_ = v_isSharedCheck_621_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_fst_495_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_621_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_next_538_; lean_object* v_upperBound_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v_next_538_ = lean_ctor_get(v_fst_491_, 0);
lean_inc(v_next_538_);
v_upperBound_539_ = lean_ctor_get(v_fst_491_, 1);
v___x_540_ = lean_array_fget(v_array_516_, v_start_517_);
v___x_541_ = lean_nat_add(v_start_517_, v___x_520_);
lean_dec(v_start_517_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_541_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_array_516_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_stop_518_);
v___x_543_ = v_reuseFailAlloc_620_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
if (lean_obj_tag(v_next_538_) == 0)
{
lean_dec(v___x_540_);
lean_dec(v___x_519_);
lean_dec_ref(v_fixedArgs_470_);
goto v___jp_544_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_619_; 
v_val_555_ = lean_ctor_get(v_next_538_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_next_538_);
if (v_isSharedCheck_619_ == 0)
{
v___x_557_ = v_next_538_;
v_isShared_558_ = v_isSharedCheck_619_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v_next_538_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_619_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_lt(v_val_555_, v_upperBound_539_);
if (v___x_559_ == 0)
{
lean_del_object(v___x_557_);
lean_dec(v_val_555_);
lean_dec(v___x_540_);
lean_dec(v___x_519_);
lean_dec_ref(v_fixedArgs_470_);
goto v___jp_544_;
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_616_; 
lean_inc(v_upperBound_539_);
lean_del_object(v___x_497_);
lean_del_object(v___x_493_);
lean_del_object(v___x_489_);
v_isSharedCheck_616_ = !lean_is_exclusive(v_fst_491_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_617_ = lean_ctor_get(v_fst_491_, 1);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_fst_491_, 0);
lean_dec(v_unused_618_);
v___x_561_ = v_fst_491_;
v_isShared_562_ = v_isSharedCheck_616_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_fst_491_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_616_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_ref_563_; lean_object* v_fn_564_; lean_object* v___x_565_; lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_ref_563_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_ref_563_);
v_fn_564_ = lean_ctor_get(v___x_519_, 1);
lean_inc_ref(v_fn_564_);
lean_dec(v___x_519_);
v___x_565_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v_a_566_ = lean_array_uget_borrowed(v_as_471_, v_i_473_);
v___x_567_ = lean_nat_add(v_val_555_, v___x_520_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_567_);
v___x_569_ = v___x_557_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_615_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_569_);
v___x_571_ = v___x_561_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_upperBound_539_);
v___x_571_ = v_reuseFailAlloc_614_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
v___x_572_ = lean_infer_type(v_fn_564_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v_perms_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v_perms_574_ = lean_ctor_get(v_fixedParamPerms_469_, 1);
v___x_575_ = lean_array_get_borrowed(v___x_565_, v_perms_574_, v_val_555_);
lean_dec(v_val_555_);
lean_inc_ref(v_fixedArgs_470_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_575_, v_a_573_, v_fixedArgs_470_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___f_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_n(v_a_577_, 2);
lean_dec_ref_known(v___x_576_, 1);
lean_inc(v_a_566_);
lean_inc(v___x_540_);
v___f_578_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(v___f_578_, 0, v___x_540_);
lean_closure_set(v___f_578_, 1, v_a_566_);
lean_closure_set(v___f_578_, 2, v_a_577_);
lean_closure_set(v___f_578_, 3, v_ref_563_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_540_);
v___x_580_ = 0;
v___x_581_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_a_577_, v___x_579_, v___f_578_, v___x_580_, v___x_580_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; size_t v___x_587_; size_t v___x_588_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_array_push(v_fst_487_, v_a_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_543_);
lean_ctor_set(v___x_584_, 1, v___x_523_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_571_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_583_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_473_, v___x_587_);
v_i_473_ = v___x_588_;
v_b_474_ = v___x_586_;
goto _start;
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___x_571_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_523_);
lean_dec(v_fst_487_);
lean_dec_ref(v_fixedArgs_470_);
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v___x_571_);
lean_dec(v_ref_563_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_523_);
lean_dec(v_fst_487_);
lean_dec_ref(v_fixedArgs_470_);
v_a_598_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_576_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_576_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v___x_571_);
lean_dec(v_ref_563_);
lean_dec(v_val_555_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_523_);
lean_dec(v_fst_487_);
lean_dec_ref(v_fixedArgs_470_);
v_a_606_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_572_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_572_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
}
}
v___jp_544_:
{
lean_object* v___x_546_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_523_);
lean_ctor_set(v___x_497_, 0, v___x_543_);
v___x_546_ = v___x_497_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_523_);
v___x_546_ = v_reuseFailAlloc_554_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_546_);
v___x_548_ = v___x_493_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_546_);
v___x_548_ = v_reuseFailAlloc_553_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_548_);
v___x_550_ = v___x_489_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_469_ = stack[0].m_obj;
lean_object* v_fixedArgs_470_ = stack[1].m_obj;
lean_object* v_as_471_ = stack[2].m_obj;
size_t v_sz_472_ = stack[3].m_num;
size_t v_i_473_ = stack[4].m_num;
lean_object* v_b_474_ = stack[5].m_obj;
lean_object* v___y_475_ = stack[6].m_obj;
lean_object* v___y_476_ = stack[7].m_obj;
lean_object* v___y_477_ = stack[8].m_obj;
lean_object* v___y_478_ = stack[9].m_obj;
lean_object* v___y_479_ = stack[10].m_obj;
lean_object* v___y_480_ = stack[11].m_obj;
lean_object* v_res_636_;
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_469_, v_fixedArgs_470_, v_as_471_, v_sz_472_, v_i_473_, v_b_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object* v_fixedParamPerms_637_, lean_object* v_fixedArgs_638_, lean_object* v_as_639_, lean_object* v_sz_640_, lean_object* v_i_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
size_t v_sz_boxed_650_; size_t v_i_boxed_651_; lean_object* v_res_652_; 
v_sz_boxed_650_ = lean_unbox_usize(v_sz_640_);
lean_dec(v_sz_640_);
v_i_boxed_651_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_637_, v_fixedArgs_638_, v_as_639_, v_sz_boxed_650_, v_i_boxed_651_, v_b_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v_as_639_);
lean_dec_ref(v_fixedParamPerms_637_);
return v_res_652_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object* v_upperBound_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_termMeasures_668_, lean_object* v_names_669_, lean_object* v_a_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_a_680_; uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_lt(v_a_670_, v_upperBound_665_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v_a_670_);
lean_dec_ref(v___x_667_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_671_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
v___x_687_ = lean_box(0);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_box(0);
v___x_690_ = lean_array_fget_borrowed(v___x_666_, v_a_670_);
lean_inc(v___x_690_);
lean_inc_ref(v___x_667_);
v___x_691_ = l_Lean_Meta_isExprDefEqGuarded(v___x_667_, v___x_690_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; uint8_t v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = lean_unbox(v_a_692_);
lean_dec(v_a_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v_ref_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_694_ = lean_array_get_borrowed(v___x_686_, v_termMeasures_668_, v_a_670_);
v_ref_695_ = lean_ctor_get(v___x_694_, 0);
v___x_696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
v___x_697_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
v___x_698_ = lean_array_get_borrowed(v___x_687_, v_names_669_, v___x_688_);
lean_inc(v___x_698_);
v___x_699_ = l_Lean_MessageData_ofName(v___x_698_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_697_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_696_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
lean_inc_ref(v___x_667_);
v___x_704_ = l_Lean_indentExpr(v___x_667_);
v___x_705_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_703_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
v___x_709_ = lean_array_get_borrowed(v___x_687_, v_names_669_, v_a_670_);
lean_inc(v___x_709_);
v___x_710_ = l_Lean_MessageData_ofName(v___x_709_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_701_);
lean_inc(v___x_690_);
v___x_713_ = l_Lean_indentExpr(v___x_690_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_705_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_707_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_695_, v___x_718_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_dec_ref_known(v___x_719_, 1);
v_a_680_ = v___x_689_;
goto v___jp_679_;
}
else
{
lean_dec(v_a_670_);
lean_dec_ref(v___x_667_);
return v___x_719_;
}
}
else
{
v_a_680_ = v___x_689_;
goto v___jp_679_;
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_670_);
lean_dec_ref(v___x_667_);
v_a_720_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_691_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_691_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_a_670_, v___x_681_);
lean_dec(v_a_670_);
v_a_670_ = v___x_682_;
v_b_671_ = v_a_680_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_665_ = stack[0].m_obj;
lean_object* v___x_666_ = stack[1].m_obj;
lean_object* v___x_667_ = stack[2].m_obj;
lean_object* v_termMeasures_668_ = stack[3].m_obj;
lean_object* v_names_669_ = stack[4].m_obj;
lean_object* v_a_670_ = stack[5].m_obj;
lean_object* v_b_671_ = stack[6].m_obj;
lean_object* v___y_672_ = stack[7].m_obj;
lean_object* v___y_673_ = stack[8].m_obj;
lean_object* v___y_674_ = stack[9].m_obj;
lean_object* v___y_675_ = stack[10].m_obj;
lean_object* v___y_676_ = stack[11].m_obj;
lean_object* v___y_677_ = stack[12].m_obj;
lean_object* v_res_728_;
v_res_728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_665_, v___x_666_, v___x_667_, v_termMeasures_668_, v_names_669_, v_a_670_, v_b_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
stack->m_obj
 = v_res_728_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object* v_upperBound_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_termMeasures_732_, lean_object* v_names_733_, lean_object* v_a_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_729_, v___x_730_, v___x_731_, v_termMeasures_732_, v_names_733_, v_a_734_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_names_733_);
lean_dec_ref(v_termMeasures_732_);
lean_dec_ref(v___x_730_);
lean_dec(v_upperBound_729_);
return v_res_743_;
}
}
lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* v_names_748_, lean_object* v_fixedParamPerms_749_, lean_object* v_fixedArgs_750_, lean_object* v_arities_751_, lean_object* v_termMeasures_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_codomains_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_760_ = l_Lean_instInhabitedExpr;
v___x_761_ = lean_unsigned_to_nat(0u);
v_codomains_762_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__0));
v___x_763_ = lean_array_get_size(v_names_748_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__1));
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
v___x_766_ = lean_array_get_size(v_arities_751_);
v___x_767_ = l_Array_toSubarray___redArg(v_arities_751_, v___x_761_, v___x_766_);
v___x_768_ = lean_array_get_size(v_termMeasures_752_);
lean_inc_ref(v_termMeasures_752_);
v___x_769_ = l_Array_toSubarray___redArg(v_termMeasures_752_, v___x_761_, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_765_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_codomains_762_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v_sz_773_ = lean_array_size(v_names_748_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_749_, v_fixedArgs_750_, v_names_748_, v_sz_773_, v___x_774_, v___x_772_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v_fst_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v_fst_777_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_fst_777_);
lean_dec(v_a_776_);
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_array_get_size(v_fst_777_);
v___x_780_ = lean_array_get(v___x_760_, v_fst_777_, v___x_761_);
v___x_781_ = lean_box(0);
lean_inc(v___x_780_);
v___x_782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v___x_779_, v_fst_777_, v___x_780_, v_termMeasures_752_, v_names_748_, v___x_778_, v___x_781_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec_ref(v_termMeasures_752_);
lean_dec(v_fst_777_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_782_, 0);
lean_dec(v_unused_790_);
v___x_784_ = v___x_782_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_dec(v___x_782_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_780_);
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_780_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v___x_780_);
v_a_791_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_782_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_782_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_termMeasures_752_);
v_a_799_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_775_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_775_);
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
LEAN_EXPORT void l_Lean_Elab_WF_checkCodomains_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_748_ = stack[0].m_obj;
lean_object* v_fixedParamPerms_749_ = stack[1].m_obj;
lean_object* v_fixedArgs_750_ = stack[2].m_obj;
lean_object* v_arities_751_ = stack[3].m_obj;
lean_object* v_termMeasures_752_ = stack[4].m_obj;
lean_object* v_a_753_ = stack[5].m_obj;
lean_object* v_a_754_ = stack[6].m_obj;
lean_object* v_a_755_ = stack[7].m_obj;
lean_object* v_a_756_ = stack[8].m_obj;
lean_object* v_a_757_ = stack[9].m_obj;
lean_object* v_a_758_ = stack[10].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_Elab_WF_checkCodomains(v_names_748_, v_fixedParamPerms_749_, v_fixedArgs_750_, v_arities_751_, v_termMeasures_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* v_names_808_, lean_object* v_fixedParamPerms_809_, lean_object* v_fixedArgs_810_, lean_object* v_arities_811_, lean_object* v_termMeasures_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Elab_WF_checkCodomains(v_names_808_, v_fixedParamPerms_809_, v_fixedArgs_810_, v_arities_811_, v_termMeasures_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec_ref(v_fixedParamPerms_809_);
lean_dec_ref(v_names_808_);
return v_res_820_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object* v_00_u03b1_821_, lean_object* v_ref_822_, lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_822_, v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_831_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_822_ = stack[1].m_obj;
lean_object* v_msg_823_ = stack[2].m_obj;
lean_object* v___y_824_ = stack[3].m_obj;
lean_object* v___y_825_ = stack[4].m_obj;
lean_object* v___y_826_ = stack[5].m_obj;
lean_object* v___y_827_ = stack[6].m_obj;
lean_object* v___y_828_ = stack[7].m_obj;
lean_object* v___y_829_ = stack[8].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_box(0), v_ref_822_, v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object* v_00_u03b1_833_, lean_object* v_ref_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(v_00_u03b1_833_, v_ref_834_, v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_ref_834_);
return v_res_843_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object* v_upperBound_844_, lean_object* v___x_845_, lean_object* v___x_846_, lean_object* v_termMeasures_847_, lean_object* v_names_848_, lean_object* v_inst_849_, lean_object* v_R_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v_c_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_844_, v___x_845_, v___x_846_, v_termMeasures_847_, v_names_848_, v_a_851_, v_b_852_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_844_ = stack[0].m_obj;
lean_object* v___x_845_ = stack[1].m_obj;
lean_object* v___x_846_ = stack[2].m_obj;
lean_object* v_termMeasures_847_ = stack[3].m_obj;
lean_object* v_names_848_ = stack[4].m_obj;
lean_object* v_a_851_ = stack[7].m_obj;
lean_object* v_b_852_ = stack[8].m_obj;
lean_object* v___y_854_ = stack[10].m_obj;
lean_object* v___y_855_ = stack[11].m_obj;
lean_object* v___y_856_ = stack[12].m_obj;
lean_object* v___y_857_ = stack[13].m_obj;
lean_object* v___y_858_ = stack[14].m_obj;
lean_object* v___y_859_ = stack[15].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(v_upperBound_844_, v___x_845_, v___x_846_, v_termMeasures_847_, v_names_848_, lean_box(0), lean_box(0), v_a_851_, v_b_852_, lean_box(0), v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_863_ = _args[0];
lean_object* v___x_864_ = _args[1];
lean_object* v___x_865_ = _args[2];
lean_object* v_termMeasures_866_ = _args[3];
lean_object* v_names_867_ = _args[4];
lean_object* v_inst_868_ = _args[5];
lean_object* v_R_869_ = _args[6];
lean_object* v_a_870_ = _args[7];
lean_object* v_b_871_ = _args[8];
lean_object* v_c_872_ = _args[9];
lean_object* v___y_873_ = _args[10];
lean_object* v___y_874_ = _args[11];
lean_object* v___y_875_ = _args[12];
lean_object* v___y_876_ = _args[13];
lean_object* v___y_877_ = _args[14];
lean_object* v___y_878_ = _args[15];
lean_object* v___y_879_ = _args[16];
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(v_upperBound_863_, v___x_864_, v___x_865_, v_termMeasures_866_, v_names_867_, v_inst_868_, v_R_869_, v_a_870_, v_b_871_, v_c_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v_names_867_);
lean_dec_ref(v_termMeasures_866_);
lean_dec_ref(v___x_864_);
lean_dec(v_upperBound_863_);
return v_res_880_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object* v_00_u03b1_881_, lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_890_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_882_ = stack[1].m_obj;
lean_object* v___y_883_ = stack[2].m_obj;
lean_object* v___y_884_ = stack[3].m_obj;
lean_object* v___y_885_ = stack[4].m_obj;
lean_object* v___y_886_ = stack[5].m_obj;
lean_object* v___y_887_ = stack[6].m_obj;
lean_object* v___y_888_ = stack[7].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_box(0), v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object* v_00_u03b1_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(v_00_u03b1_892_, v_msg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_901_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object* v_msgData_902_, lean_object* v_macroStack_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_902_, v_macroStack_903_, v___y_908_);
return v___x_911_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_902_ = stack[0].m_obj;
lean_object* v_macroStack_903_ = stack[1].m_obj;
lean_object* v___y_904_ = stack[2].m_obj;
lean_object* v___y_905_ = stack[3].m_obj;
lean_object* v___y_906_ = stack[4].m_obj;
lean_object* v___y_907_ = stack[5].m_obj;
lean_object* v___y_908_ = stack[6].m_obj;
lean_object* v___y_909_ = stack[7].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_902_, v_macroStack_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_913_, lean_object* v_macroStack_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_913_, v_macroStack_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_922_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object* v_e_923_, lean_object* v___y_924_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_Expr_hasMVar(v_e_923_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_e_923_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v_mctx_929_; lean_object* v___x_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___x_933_; lean_object* v_cache_934_; lean_object* v_zetaDeltaFVarIds_935_; lean_object* v_postponed_936_; lean_object* v_diag_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_946_; 
v___x_928_ = lean_st_ref_get(v___y_924_);
v_mctx_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_mctx_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_instantiateMVarsCore(v_mctx_929_, v_e_923_);
v_fst_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_fst_931_);
v_snd_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v___x_930_);
v___x_933_ = lean_st_ref_take(v___y_924_);
v_cache_934_ = lean_ctor_get(v___x_933_, 1);
v_zetaDeltaFVarIds_935_ = lean_ctor_get(v___x_933_, 2);
v_postponed_936_ = lean_ctor_get(v___x_933_, 3);
v_diag_937_ = lean_ctor_get(v___x_933_, 4);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_933_, 0);
lean_dec(v_unused_947_);
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_diag_937_);
lean_inc(v_postponed_936_);
lean_inc(v_zetaDeltaFVarIds_935_);
lean_inc(v_cache_934_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_snd_932_);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_snd_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_cache_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_936_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_937_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v___y_924_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_fst_931_);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_923_ = stack[0].m_obj;
lean_object* v___y_924_ = stack[1].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_923_, v___y_924_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object* v_e_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_949_, v___y_950_);
lean_dec(v___y_950_);
return v_res_952_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object* v_e_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_953_, v___y_957_);
return v___x_961_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_953_ = stack[0].m_obj;
lean_object* v___y_954_ = stack[1].m_obj;
lean_object* v___y_955_ = stack[2].m_obj;
lean_object* v___y_956_ = stack[3].m_obj;
lean_object* v___y_957_ = stack[4].m_obj;
lean_object* v___y_958_ = stack[5].m_obj;
lean_object* v___y_959_ = stack[6].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(v_e_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object* v_e_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(v_e_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_971_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object* v_fixedParamPerms_972_, lean_object* v_fixedArgs_973_, size_t v_sz_974_, size_t v_i_975_, lean_object* v_bs_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_dec_ref(v_fixedArgs_973_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_bs_976_);
return v___x_983_;
}
else
{
lean_object* v_v_984_; lean_object* v_perms_985_; lean_object* v_fn_986_; lean_object* v___x_987_; lean_object* v_bs_x27_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_v_984_ = lean_array_uget_borrowed(v_bs_976_, v_i_975_);
v_perms_985_ = lean_ctor_get(v_fixedParamPerms_972_, 1);
v_fn_986_ = lean_ctor_get(v_v_984_, 1);
lean_inc_ref(v_fn_986_);
v___x_987_ = lean_unsigned_to_nat(0u);
v_bs_x27_988_ = lean_array_uset(v_bs_976_, v_i_975_, v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_990_ = lean_usize_to_nat(v_i_975_);
v___x_991_ = lean_array_get_borrowed(v___x_989_, v_perms_985_, v___x_990_);
lean_dec(v___x_990_);
lean_inc_ref(v_fixedArgs_973_);
lean_inc(v___x_991_);
v___x_992_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_991_, v_fn_986_, v_fixedArgs_973_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_975_, v___x_994_);
v___x_996_ = lean_array_uset(v_bs_x27_988_, v_i_975_, v_a_993_);
v_i_975_ = v___x_995_;
v_bs_976_ = v___x_996_;
goto _start;
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_bs_x27_988_);
lean_dec_ref(v_fixedArgs_973_);
v_a_998_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_992_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_992_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_972_ = stack[0].m_obj;
lean_object* v_fixedArgs_973_ = stack[1].m_obj;
size_t v_sz_974_ = stack[2].m_num;
size_t v_i_975_ = stack[3].m_num;
lean_object* v_bs_976_ = stack[4].m_obj;
lean_object* v___y_977_ = stack[5].m_obj;
lean_object* v___y_978_ = stack[6].m_obj;
lean_object* v___y_979_ = stack[7].m_obj;
lean_object* v___y_980_ = stack[8].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_972_, v_fixedArgs_973_, v_sz_974_, v_i_975_, v_bs_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object* v_fixedParamPerms_1007_, lean_object* v_fixedArgs_1008_, lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_bs_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1007_, v_fixedArgs_1008_, v_sz_boxed_1017_, v_i_boxed_1018_, v_bs_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_fixedParamPerms_1007_);
return v_res_1019_;
}
}
lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object* v_argType_1026_, lean_object* v_argsPacker_1027_, lean_object* v_declNames_1028_, lean_object* v_fixedParamPerms_1029_, lean_object* v_fixedArgs_1030_, lean_object* v_termMeasures_1031_, lean_object* v_k_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
lean_inc_ref(v_argType_1026_);
v___x_1040_ = l_Lean_Meta_getLevel(v_argType_1026_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
lean_inc_ref(v_argsPacker_1027_);
v___x_1042_ = l_Lean_Meta_ArgsPacker_arities(v_argsPacker_1027_);
lean_inc_ref(v_termMeasures_1031_);
lean_inc_ref(v_fixedArgs_1030_);
v___x_1043_ = l_Lean_Elab_WF_checkCodomains(v_declNames_1028_, v_fixedParamPerms_1029_, v_fixedArgs_1030_, v___x_1042_, v_termMeasures_1031_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_n(v_a_1044_, 2);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_Lean_Meta_getLevel(v_a_1044_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; size_t v_sz_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_sz_1047_ = lean_array_size(v_termMeasures_1031_);
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1029_, v_fixedArgs_1030_, v_sz_1047_, v___x_1048_, v_termMeasures_1031_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_1027_, v_a_1050_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v_a_1050_);
lean_dec_ref(v_argsPacker_1027_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1));
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1046_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
lean_inc_ref(v___x_1055_);
v___x_1056_ = l_Lean_Expr_const___override(v___x_1053_, v___x_1055_);
lean_inc(v_a_1044_);
v___x_1057_ = l_Lean_Expr_app___override(v___x_1056_, v_a_1044_);
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Lean_Meta_synthInstance(v___x_1057_, v___x_1058_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3));
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1041_);
lean_ctor_set(v___x_1062_, 1, v___x_1055_);
v___x_1063_ = l_Lean_Expr_const___override(v___x_1061_, v___x_1062_);
v___x_1064_ = l_Lean_mkApp4(v___x_1063_, v_argType_1026_, v_a_1044_, v_a_1052_, v_a_1060_);
v___x_1065_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v___x_1064_, v___y_1036_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = lean_apply_8(v_k_1032_, v_a_1066_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, lean_box(0));
return v___x_1067_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref_known(v___x_1055_, 2);
lean_dec(v_a_1052_);
lean_dec(v_a_1044_);
lean_dec(v_a_1041_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_argType_1026_);
v_a_1068_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1059_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1059_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1046_);
lean_dec(v_a_1044_);
lean_dec(v_a_1041_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_argType_1026_);
v_a_1076_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1051_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1051_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1046_);
lean_dec(v_a_1044_);
lean_dec(v_a_1041_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_argsPacker_1027_);
lean_dec_ref(v_argType_1026_);
v_a_1084_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1049_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1049_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1044_);
lean_dec(v_a_1041_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_termMeasures_1031_);
lean_dec_ref(v_fixedArgs_1030_);
lean_dec_ref(v_argsPacker_1027_);
lean_dec_ref(v_argType_1026_);
v_a_1092_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1045_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1045_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1041_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_termMeasures_1031_);
lean_dec_ref(v_fixedArgs_1030_);
lean_dec_ref(v_argsPacker_1027_);
lean_dec_ref(v_argType_1026_);
v_a_1100_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1043_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1043_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_termMeasures_1031_);
lean_dec_ref(v_fixedArgs_1030_);
lean_dec_ref(v_argsPacker_1027_);
lean_dec_ref(v_argType_1026_);
v_a_1108_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1040_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1040_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_elabWFRel___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_argType_1026_ = stack[0].m_obj;
lean_object* v_argsPacker_1027_ = stack[1].m_obj;
lean_object* v_declNames_1028_ = stack[2].m_obj;
lean_object* v_fixedParamPerms_1029_ = stack[3].m_obj;
lean_object* v_fixedArgs_1030_ = stack[4].m_obj;
lean_object* v_termMeasures_1031_ = stack[5].m_obj;
lean_object* v_k_1032_ = stack[6].m_obj;
lean_object* v___y_1033_ = stack[7].m_obj;
lean_object* v___y_1034_ = stack[8].m_obj;
lean_object* v___y_1035_ = stack[9].m_obj;
lean_object* v___y_1036_ = stack[10].m_obj;
lean_object* v___y_1037_ = stack[11].m_obj;
lean_object* v___y_1038_ = stack[12].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(v_argType_1026_, v_argsPacker_1027_, v_declNames_1028_, v_fixedParamPerms_1029_, v_fixedArgs_1030_, v_termMeasures_1031_, v_k_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object* v_argType_1117_, lean_object* v_argsPacker_1118_, lean_object* v_declNames_1119_, lean_object* v_fixedParamPerms_1120_, lean_object* v_fixedArgs_1121_, lean_object* v_termMeasures_1122_, lean_object* v_k_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(v_argType_1117_, v_argsPacker_1118_, v_declNames_1119_, v_fixedParamPerms_1120_, v_fixedArgs_1121_, v_termMeasures_1122_, v_k_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v_fixedParamPerms_1120_);
lean_dec_ref(v_declNames_1119_);
return v_res_1131_;
}
}
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object* v_declNames_1132_, lean_object* v_unaryPreDefName_1133_, lean_object* v_fixedParamPerms_1134_, lean_object* v_fixedArgs_1135_, lean_object* v_argsPacker_1136_, lean_object* v_argType_1137_, lean_object* v_termMeasures_1138_, lean_object* v_k_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___f_1147_; lean_object* v___x_1148_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1147_, 0, v_argType_1137_);
lean_closure_set(v___f_1147_, 1, v_argsPacker_1136_);
lean_closure_set(v___f_1147_, 2, v_declNames_1132_);
lean_closure_set(v___f_1147_, 3, v_fixedParamPerms_1134_);
lean_closure_set(v___f_1147_, 4, v_fixedArgs_1135_);
lean_closure_set(v___f_1147_, 5, v_termMeasures_1138_);
lean_closure_set(v___f_1147_, 6, v_k_1139_);
v___x_1148_ = l_Lean_Elab_Term_withDeclName___redArg(v_unaryPreDefName_1133_, v___f_1147_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v___x_1148_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_elabWFRel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_1132_ = stack[0].m_obj;
lean_object* v_unaryPreDefName_1133_ = stack[1].m_obj;
lean_object* v_fixedParamPerms_1134_ = stack[2].m_obj;
lean_object* v_fixedArgs_1135_ = stack[3].m_obj;
lean_object* v_argsPacker_1136_ = stack[4].m_obj;
lean_object* v_argType_1137_ = stack[5].m_obj;
lean_object* v_termMeasures_1138_ = stack[6].m_obj;
lean_object* v_k_1139_ = stack[7].m_obj;
lean_object* v_a_1140_ = stack[8].m_obj;
lean_object* v_a_1141_ = stack[9].m_obj;
lean_object* v_a_1142_ = stack[10].m_obj;
lean_object* v_a_1143_ = stack[11].m_obj;
lean_object* v_a_1144_ = stack[12].m_obj;
lean_object* v_a_1145_ = stack[13].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1132_, v_unaryPreDefName_1133_, v_fixedParamPerms_1134_, v_fixedArgs_1135_, v_argsPacker_1136_, v_argType_1137_, v_termMeasures_1138_, v_k_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object* v_declNames_1150_, lean_object* v_unaryPreDefName_1151_, lean_object* v_fixedParamPerms_1152_, lean_object* v_fixedArgs_1153_, lean_object* v_argsPacker_1154_, lean_object* v_argType_1155_, lean_object* v_termMeasures_1156_, lean_object* v_k_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1150_, v_unaryPreDefName_1151_, v_fixedParamPerms_1152_, v_fixedArgs_1153_, v_argsPacker_1154_, v_argType_1155_, v_termMeasures_1156_, v_k_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1165_;
}
}
lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* v_00_u03b1_1166_, lean_object* v_declNames_1167_, lean_object* v_unaryPreDefName_1168_, lean_object* v_fixedParamPerms_1169_, lean_object* v_fixedArgs_1170_, lean_object* v_argsPacker_1171_, lean_object* v_argType_1172_, lean_object* v_termMeasures_1173_, lean_object* v_k_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1167_, v_unaryPreDefName_1168_, v_fixedParamPerms_1169_, v_fixedArgs_1170_, v_argsPacker_1171_, v_argType_1172_, v_termMeasures_1173_, v_k_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_elabWFRel_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_1167_ = stack[1].m_obj;
lean_object* v_unaryPreDefName_1168_ = stack[2].m_obj;
lean_object* v_fixedParamPerms_1169_ = stack[3].m_obj;
lean_object* v_fixedArgs_1170_ = stack[4].m_obj;
lean_object* v_argsPacker_1171_ = stack[5].m_obj;
lean_object* v_argType_1172_ = stack[6].m_obj;
lean_object* v_termMeasures_1173_ = stack[7].m_obj;
lean_object* v_k_1174_ = stack[8].m_obj;
lean_object* v_a_1175_ = stack[9].m_obj;
lean_object* v_a_1176_ = stack[10].m_obj;
lean_object* v_a_1177_ = stack[11].m_obj;
lean_object* v_a_1178_ = stack[12].m_obj;
lean_object* v_a_1179_ = stack[13].m_obj;
lean_object* v_a_1180_ = stack[14].m_obj;
lean_object* v_res_1183_;
v_res_1183_ = l_Lean_Elab_WF_elabWFRel(lean_box(0), v_declNames_1167_, v_unaryPreDefName_1168_, v_fixedParamPerms_1169_, v_fixedArgs_1170_, v_argsPacker_1171_, v_argType_1172_, v_termMeasures_1173_, v_k_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
stack->m_obj
 = v_res_1183_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_declNames_1185_, lean_object* v_unaryPreDefName_1186_, lean_object* v_fixedParamPerms_1187_, lean_object* v_fixedArgs_1188_, lean_object* v_argsPacker_1189_, lean_object* v_argType_1190_, lean_object* v_termMeasures_1191_, lean_object* v_k_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Elab_WF_elabWFRel(v_00_u03b1_1184_, v_declNames_1185_, v_unaryPreDefName_1186_, v_fixedParamPerms_1187_, v_fixedArgs_1188_, v_argsPacker_1189_, v_argType_1190_, v_termMeasures_1191_, v_k_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1200_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object* v_fixedParamPerms_1201_, lean_object* v_fixedArgs_1202_, lean_object* v_as_1203_, size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_bs_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1201_, v_fixedArgs_1202_, v_sz_1204_, v_i_1205_, v_bs_1206_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_1201_ = stack[0].m_obj;
lean_object* v_fixedArgs_1202_ = stack[1].m_obj;
lean_object* v_as_1203_ = stack[2].m_obj;
size_t v_sz_1204_ = stack[3].m_num;
size_t v_i_1205_ = stack[4].m_num;
lean_object* v_bs_1206_ = stack[5].m_obj;
lean_object* v___y_1207_ = stack[6].m_obj;
lean_object* v___y_1208_ = stack[7].m_obj;
lean_object* v___y_1209_ = stack[8].m_obj;
lean_object* v___y_1210_ = stack[9].m_obj;
lean_object* v___y_1211_ = stack[10].m_obj;
lean_object* v___y_1212_ = stack[11].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(v_fixedParamPerms_1201_, v_fixedArgs_1202_, v_as_1203_, v_sz_1204_, v_i_1205_, v_bs_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object* v_fixedParamPerms_1216_, lean_object* v_fixedArgs_1217_, lean_object* v_as_1218_, lean_object* v_sz_1219_, lean_object* v_i_1220_, lean_object* v_bs_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
size_t v_sz_boxed_1229_; size_t v_i_boxed_1230_; lean_object* v_res_1231_; 
v_sz_boxed_1229_ = lean_unbox_usize(v_sz_1219_);
lean_dec(v_sz_1219_);
v_i_boxed_1230_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(v_fixedParamPerms_1216_, v_fixedArgs_1217_, v_as_1218_, v_sz_boxed_1229_, v_i_boxed_1230_, v_bs_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v_as_1218_);
lean_dec_ref(v_fixedParamPerms_1216_);
return v_res_1231_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
