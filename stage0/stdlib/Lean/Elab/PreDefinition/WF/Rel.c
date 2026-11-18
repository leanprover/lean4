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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_133_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_131_, v_as_130_, v___x_135_, v___x_136_);
return v___x_137_;
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
uint8_t v___x_144_; lean_object* v_d_146_; lean_object* v_b_147_; 
v___x_144_ = l_Lean_Expr_hasFVar(v_e_143_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
switch(lean_obj_tag(v_e_143_))
{
case 7:
{
lean_object* v_binderType_150_; lean_object* v_body_151_; 
v_binderType_150_ = lean_ctor_get(v_e_143_, 1);
v_body_151_ = lean_ctor_get(v_e_143_, 2);
v_d_146_ = v_binderType_150_;
v_b_147_ = v_body_151_;
goto v___jp_145_;
}
case 6:
{
lean_object* v_binderType_152_; lean_object* v_body_153_; 
v_binderType_152_ = lean_ctor_get(v_e_143_, 1);
v_body_153_ = lean_ctor_get(v_e_143_, 2);
v_d_146_ = v_binderType_152_;
v_b_147_ = v_body_153_;
goto v___jp_145_;
}
case 10:
{
lean_object* v_expr_154_; 
v_expr_154_ = lean_ctor_get(v_e_143_, 1);
v_e_143_ = v_expr_154_;
goto _start;
}
case 8:
{
lean_object* v_type_156_; lean_object* v_value_157_; lean_object* v_body_158_; uint8_t v___x_159_; 
v_type_156_ = lean_ctor_get(v_e_143_, 1);
v_value_157_ = lean_ctor_get(v_e_143_, 2);
v_body_158_ = lean_ctor_get(v_e_143_, 3);
v___x_159_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_type_156_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_value_157_);
if (v___x_160_ == 0)
{
v_e_143_ = v_body_158_;
goto _start;
}
else
{
return v___x_144_;
}
}
else
{
return v___x_144_;
}
}
case 5:
{
lean_object* v_fn_162_; lean_object* v_arg_163_; uint8_t v___x_164_; 
v_fn_162_ = lean_ctor_get(v_e_143_, 0);
v_arg_163_ = lean_ctor_get(v_e_143_, 1);
v___x_164_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_fn_162_);
if (v___x_164_ == 0)
{
v_e_143_ = v_arg_163_;
goto _start;
}
else
{
return v___x_144_;
}
}
case 11:
{
lean_object* v_struct_166_; 
v_struct_166_ = lean_ctor_get(v_e_143_, 2);
v_e_143_ = v_struct_166_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_168_; uint8_t v___x_169_; 
v_fvarId_168_ = lean_ctor_get(v_e_143_, 0);
v___x_169_ = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v___x_142_, v_fvarId_168_);
return v___x_169_;
}
default: 
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
v___jp_145_:
{
uint8_t v___x_148_; 
v___x_148_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_142_, v_d_146_);
if (v___x_148_ == 0)
{
v_e_143_ = v_b_147_;
goto _start;
}
else
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object* v___x_171_, lean_object* v_e_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_171_, v_e_172_);
lean_dec_ref(v_e_172_);
lean_dec_ref(v___x_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t v_sz_175_, size_t v_i_176_, lean_object* v_bs_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_usize_dec_lt(v_i_176_, v_sz_175_);
if (v___x_178_ == 0)
{
return v_bs_177_;
}
else
{
lean_object* v_v_179_; lean_object* v___x_180_; lean_object* v_bs_x27_181_; lean_object* v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; 
v_v_179_ = lean_array_uget(v_bs_177_, v_i_176_);
v___x_180_ = lean_unsigned_to_nat(0u);
v_bs_x27_181_ = lean_array_uset(v_bs_177_, v_i_176_, v___x_180_);
v___x_182_ = l_Lean_Expr_fvarId_x21(v_v_179_);
lean_dec(v_v_179_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_add(v_i_176_, v___x_183_);
v___x_185_ = lean_array_uset(v_bs_x27_181_, v_i_176_, v___x_182_);
v_i_176_ = v___x_184_;
v_bs_177_ = v___x_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object* v_sz_187_, lean_object* v_i_188_, lean_object* v_bs_189_){
_start:
{
size_t v_sz_boxed_190_; size_t v_i_boxed_191_; lean_object* v_res_192_; 
v_sz_boxed_190_ = lean_unbox_usize(v_sz_187_);
lean_dec(v_sz_187_);
v_i_boxed_191_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_boxed_190_, v_i_boxed_191_, v_bs_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; uint8_t v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v_toCold_204_; lean_object* v_mctx_205_; lean_object* v_lctx_206_; lean_object* v_options_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v___x_201_ = 0;
v_env_202_ = l_Lean_Environment_setRecordingDeps(v_env_200_, v___x_201_);
v___x_203_ = lean_st_ref_get(v___y_195_);
v_toCold_204_ = lean_ctor_get(v___y_196_, 0);
v_mctx_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_mctx_205_);
lean_dec(v___x_203_);
v_lctx_206_ = lean_ctor_get(v___y_194_, 2);
v_options_207_ = lean_ctor_get(v_toCold_204_, 2);
lean_inc_ref(v_options_207_);
lean_inc_ref(v_lctx_206_);
v___x_208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_208_, 0, v_env_202_);
lean_ctor_set(v___x_208_, 1, v_mctx_205_);
lean_ctor_set(v___x_208_, 2, v_lctx_206_);
lean_ctor_set(v___x_208_, 3, v_options_207_);
v___x_209_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_msgData_193_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object* v_msgData_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object* v_opts_218_, lean_object* v_opt_219_){
_start:
{
lean_object* v_name_220_; lean_object* v_defValue_221_; lean_object* v_map_222_; lean_object* v___x_223_; 
v_name_220_ = lean_ctor_get(v_opt_219_, 0);
v_defValue_221_ = lean_ctor_get(v_opt_219_, 1);
v_map_222_ = lean_ctor_get(v_opts_218_, 0);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_222_, v_name_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_defValue_221_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_223_, 1);
if (lean_obj_tag(v_val_225_) == 1)
{
uint8_t v_v_226_; 
v_v_226_ = lean_ctor_get_uint8(v_val_225_, 0);
lean_dec_ref_known(v_val_225_, 0);
return v_v_226_;
}
else
{
uint8_t v___x_227_; 
lean_dec(v_val_225_);
v___x_227_ = lean_unbox(v_defValue_221_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object* v_opts_228_, lean_object* v_opt_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_228_, v_opt_229_);
lean_dec_ref(v_opt_229_);
lean_dec_ref(v_opts_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(1);
v___x_233_ = l_Lean_MessageData_ofFormat(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2));
v___x_238_ = l_Lean_MessageData_ofFormat(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
return v_x_239_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_264_; 
v_head_241_ = lean_ctor_get(v_x_240_, 0);
v_tail_242_ = lean_ctor_get(v_x_240_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_264_ == 0)
{
v___x_244_ = v_x_240_;
v_isShared_245_ = v_isSharedCheck_264_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_tail_242_);
lean_inc(v_head_241_);
lean_dec(v_x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_264_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_before_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_262_; 
v_before_246_ = lean_ctor_get(v_head_241_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_head_241_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_head_241_, 1);
lean_dec(v_unused_263_);
v___x_248_ = v_head_241_;
v_isShared_249_ = v_isSharedCheck_262_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_before_246_);
lean_dec(v_head_241_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_262_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 7);
lean_ctor_set(v___x_248_, 1, v___x_250_);
lean_ctor_set(v___x_248_, 0, v_x_239_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_x_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_261_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 7);
lean_ctor_set(v___x_244_, 1, v___x_253_);
lean_ctor_set(v___x_244_, 0, v___x_252_);
v___x_255_ = v___x_244_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_253_);
v___x_255_ = v_reuseFailAlloc_260_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = l_Lean_MessageData_ofSyntax(v_before_246_);
v___x_257_ = l_Lean_indentD(v___x_256_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_255_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v_x_239_ = v___x_258_;
v_x_240_ = v_tail_242_;
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
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1));
v___x_269_ = l_Lean_MessageData_ofFormat(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object* v_msgData_270_, lean_object* v_macroStack_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_272_);
v___x_275_ = l_Lean_Elab_pp_macroStack;
v___x_276_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v___x_274_, v___x_275_);
lean_dec_ref(v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_macroStack_271_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_msgData_270_);
return v___x_277_;
}
else
{
if (lean_obj_tag(v_macroStack_271_) == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_msgData_270_);
return v___x_278_;
}
else
{
lean_object* v_head_279_; lean_object* v_after_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_295_; 
v_head_279_ = lean_ctor_get(v_macroStack_271_, 0);
lean_inc(v_head_279_);
v_after_280_ = lean_ctor_get(v_head_279_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_head_279_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_head_279_, 0);
lean_dec(v_unused_296_);
v___x_282_ = v_head_279_;
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_after_280_);
lean_dec(v_head_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 7);
lean_ctor_set(v___x_282_, 1, v___x_284_);
lean_ctor_set(v___x_282_, 0, v_msgData_270_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_msgData_270_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_294_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_msgData_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_287_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_MessageData_ofSyntax(v_after_280_);
v___x_290_ = l_Lean_indentD(v___x_289_);
v_msgData_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_291_, 0, v___x_288_);
lean_ctor_set(v_msgData_291_, 1, v___x_290_);
v___x_292_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(v_msgData_291_, v_macroStack_271_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
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
lean_object* v_ref_310_; lean_object* v_macroStack_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_ref_310_ = lean_ctor_get(v___y_307_, 2);
v_macroStack_311_ = lean_ctor_get(v___y_303_, 1);
v___x_312_ = l_Lean_Elab_getBetterRef(v_ref_310_, v_macroStack_311_);
v___x_313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msg_302_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_313_);
lean_inc(v_macroStack_311_);
v___x_315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_a_314_, v_macroStack_311_, v___y_307_);
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
lean_ctor_set(v___x_320_, 0, v___x_312_);
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
lean_object* v_toCold_343_; lean_object* v_currRecDepth_344_; lean_object* v_ref_345_; uint16_t v_optionFlags_346_; uint8_t v_suppressElabErrors_347_; uint8_t v_checkDeprecated_348_; uint8_t v_isRecordingDeps_349_; lean_object* v_ref_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_toCold_343_ = lean_ctor_get(v___y_340_, 0);
v_currRecDepth_344_ = lean_ctor_get(v___y_340_, 1);
v_ref_345_ = lean_ctor_get(v___y_340_, 2);
v_optionFlags_346_ = lean_ctor_get_uint16(v___y_340_, sizeof(void*)*3);
v_suppressElabErrors_347_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*3 + 2);
v_checkDeprecated_348_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*3 + 3);
v_isRecordingDeps_349_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*3 + 4);
v_ref_350_ = l_Lean_replaceRef(v_ref_334_, v_ref_345_);
lean_inc(v_currRecDepth_344_);
lean_inc_ref(v_toCold_343_);
v___x_351_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_351_, 0, v_toCold_343_);
lean_ctor_set(v___x_351_, 1, v_currRecDepth_344_);
lean_ctor_set(v___x_351_, 2, v_ref_350_);
lean_ctor_set_uint16(v___x_351_, sizeof(void*)*3, v_optionFlags_346_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 2, v_suppressElabErrors_347_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 3, v_checkDeprecated_348_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 4, v_isRecordingDeps_349_);
v___x_352_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___x_351_, v___y_341_);
lean_dec_ref_known(v___x_351_, 3);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object* v_ref_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_353_, v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v_ref_353_);
return v_res_362_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2));
v___x_367_ = lean_unsigned_to_nat(6u);
v___x_368_ = lean_unsigned_to_nat(33u);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1));
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0));
v___x_371_ = l_mkPanicMessageWithDecl(v___x_370_, v___x_369_, v___x_368_, v___x_367_, v___x_366_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13));
v___x_388_ = l_Lean_MessageData_ofFormat(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object* v___x_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_ref_392_, lean_object* v_xs_393_, lean_object* v_codomain_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_array_get_size(v_xs_393_);
v___x_403_ = lean_nat_dec_eq(v___x_402_, v___x_389_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_codomain_394_);
lean_dec_ref(v_xs_393_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
v___x_404_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
v___x_405_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v___x_404_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
return v___x_405_;
}
else
{
size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_sz_406_ = lean_array_size(v_xs_393_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_406_, v___x_407_, v_xs_393_);
v___x_409_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_408_, v_codomain_394_);
lean_dec_ref(v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_codomain_394_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_411_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
v___x_412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
v___x_413_ = l_Lean_MessageData_ofName(v_a_390_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_indentExpr(v_a_391_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_411_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_392_, v___x_423_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_432_);
v___x_426_ = v___x_424_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_dec(v___x_424_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_codomain_394_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_codomain_394_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_codomain_394_);
v_a_433_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_424_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_424_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object* v___x_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_ref_444_, lean_object* v_xs_445_, lean_object* v_codomain_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_441_, v_a_442_, v_a_443_, v_ref_444_, v_xs_445_, v_codomain_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v_ref_444_);
lean_dec(v___x_441_);
return v_res_454_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Array_instInhabited___redArg();
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object* v_fixedParamPerms_456_, lean_object* v_fixedArgs_457_, lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec_ref(v_fixedArgs_457_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_b_461_);
return v___x_470_;
}
else
{
lean_object* v_snd_471_; lean_object* v_snd_472_; lean_object* v_snd_473_; lean_object* v_fst_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_621_; 
v_snd_471_ = lean_ctor_get(v_b_461_, 1);
lean_inc(v_snd_471_);
v_snd_472_ = lean_ctor_get(v_snd_471_, 1);
lean_inc(v_snd_472_);
v_snd_473_ = lean_ctor_get(v_snd_472_, 1);
lean_inc(v_snd_473_);
v_fst_474_ = lean_ctor_get(v_b_461_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_b_461_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_b_461_, 1);
lean_dec(v_unused_622_);
v___x_476_ = v_b_461_;
v_isShared_477_ = v_isSharedCheck_621_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_fst_474_);
lean_dec(v_b_461_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_621_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_fst_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_619_; 
v_fst_478_ = lean_ctor_get(v_snd_471_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_snd_471_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_snd_471_, 1);
lean_dec(v_unused_620_);
v___x_480_ = v_snd_471_;
v_isShared_481_ = v_isSharedCheck_619_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_fst_478_);
lean_dec(v_snd_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_619_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_fst_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_617_; 
v_fst_482_ = lean_ctor_get(v_snd_472_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_snd_472_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_snd_472_, 1);
lean_dec(v_unused_618_);
v___x_484_ = v_snd_472_;
v_isShared_485_ = v_isSharedCheck_617_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_fst_482_);
lean_dec(v_snd_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_617_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_array_486_; lean_object* v_start_487_; lean_object* v_stop_488_; uint8_t v___x_489_; 
v_array_486_ = lean_ctor_get(v_snd_473_, 0);
v_start_487_ = lean_ctor_get(v_snd_473_, 1);
v_stop_488_ = lean_ctor_get(v_snd_473_, 2);
v___x_489_ = lean_nat_dec_lt(v_start_487_, v_stop_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v_fixedArgs_457_);
if (v_isShared_485_ == 0)
{
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_482_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_snd_473_);
v___x_491_ = v_reuseFailAlloc_499_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_491_);
v___x_493_ = v___x_480_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_fst_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_498_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_493_);
v___x_495_ = v___x_476_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_fst_474_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_497_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
}
else
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_613_; 
lean_inc(v_stop_488_);
lean_inc(v_start_487_);
lean_inc_ref(v_array_486_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_snd_473_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_614_ = lean_ctor_get(v_snd_473_, 2);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_snd_473_, 1);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_snd_473_, 0);
lean_dec(v_unused_616_);
v___x_501_ = v_snd_473_;
v_isShared_502_ = v_isSharedCheck_613_;
goto v_resetjp_500_;
}
else
{
lean_dec(v_snd_473_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_613_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_array_503_; lean_object* v_start_504_; lean_object* v_stop_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v_array_503_ = lean_ctor_get(v_fst_482_, 0);
v_start_504_ = lean_ctor_get(v_fst_482_, 1);
v_stop_505_ = lean_ctor_get(v_fst_482_, 2);
v___x_506_ = lean_array_fget(v_array_486_, v_start_487_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_start_487_, v___x_507_);
lean_dec(v_start_487_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_508_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_array_486_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_stop_488_);
v___x_510_ = v_reuseFailAlloc_612_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_lt(v_start_504_, v_stop_505_);
if (v___x_511_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v___x_506_);
lean_dec_ref(v_fixedArgs_457_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_510_);
v___x_513_ = v___x_484_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_fst_482_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_510_);
v___x_513_ = v_reuseFailAlloc_521_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_513_);
v___x_515_ = v___x_480_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_fst_478_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_520_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_515_);
v___x_517_ = v___x_476_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_fst_474_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_608_; 
lean_inc(v_stop_505_);
lean_inc(v_start_504_);
lean_inc_ref(v_array_503_);
v_isSharedCheck_608_ = !lean_is_exclusive(v_fst_482_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; lean_object* v_unused_610_; lean_object* v_unused_611_; 
v_unused_609_ = lean_ctor_get(v_fst_482_, 2);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_fst_482_, 1);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_fst_482_, 0);
lean_dec(v_unused_611_);
v___x_523_ = v_fst_482_;
v_isShared_524_ = v_isSharedCheck_608_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_fst_482_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_608_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_next_525_; lean_object* v_upperBound_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v_next_525_ = lean_ctor_get(v_fst_478_, 0);
lean_inc(v_next_525_);
v_upperBound_526_ = lean_ctor_get(v_fst_478_, 1);
v___x_527_ = lean_array_fget(v_array_503_, v_start_504_);
v___x_528_ = lean_nat_add(v_start_504_, v___x_507_);
lean_dec(v_start_504_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_528_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_array_503_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_stop_505_);
v___x_530_ = v_reuseFailAlloc_607_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
if (lean_obj_tag(v_next_525_) == 0)
{
lean_dec(v___x_527_);
lean_dec(v___x_506_);
lean_dec_ref(v_fixedArgs_457_);
goto v___jp_531_;
}
else
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_606_; 
v_val_542_ = lean_ctor_get(v_next_525_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_next_525_);
if (v_isSharedCheck_606_ == 0)
{
v___x_544_ = v_next_525_;
v_isShared_545_ = v_isSharedCheck_606_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v_next_525_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_606_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_lt(v_val_542_, v_upperBound_526_);
if (v___x_546_ == 0)
{
lean_del_object(v___x_544_);
lean_dec(v_val_542_);
lean_dec(v___x_527_);
lean_dec(v___x_506_);
lean_dec_ref(v_fixedArgs_457_);
goto v___jp_531_;
}
else
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_603_; 
lean_inc(v_upperBound_526_);
lean_del_object(v___x_484_);
lean_del_object(v___x_480_);
lean_del_object(v___x_476_);
v_isSharedCheck_603_ = !lean_is_exclusive(v_fst_478_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_604_ = lean_ctor_get(v_fst_478_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_fst_478_, 0);
lean_dec(v_unused_605_);
v___x_548_ = v_fst_478_;
v_isShared_549_ = v_isSharedCheck_603_;
goto v_resetjp_547_;
}
else
{
lean_dec(v_fst_478_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_603_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_ref_550_; lean_object* v_fn_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v_ref_550_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_ref_550_);
v_fn_551_ = lean_ctor_get(v___x_506_, 1);
lean_inc_ref(v_fn_551_);
lean_dec(v___x_506_);
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v_a_553_ = lean_array_uget_borrowed(v_as_458_, v_i_460_);
v___x_554_ = lean_nat_add(v_val_542_, v___x_507_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_554_);
v___x_556_ = v___x_544_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_602_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_556_);
v___x_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_upperBound_526_);
v___x_558_ = v_reuseFailAlloc_601_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; 
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
v___x_559_ = lean_infer_type(v_fn_551_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v_perms_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v_perms_561_ = lean_ctor_get(v_fixedParamPerms_456_, 1);
v___x_562_ = lean_array_get_borrowed(v___x_552_, v_perms_561_, v_val_542_);
lean_dec(v_val_542_);
lean_inc_ref(v_fixedArgs_457_);
lean_inc(v___x_562_);
v___x_563_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_562_, v_a_560_, v_fixedArgs_457_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___f_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_n(v_a_564_, 2);
lean_dec_ref_known(v___x_563_, 1);
lean_inc(v_a_553_);
lean_inc(v___x_527_);
v___f_565_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(v___f_565_, 0, v___x_527_);
lean_closure_set(v___f_565_, 1, v_a_553_);
lean_closure_set(v___f_565_, 2, v_a_564_);
lean_closure_set(v___f_565_, 3, v_ref_550_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_527_);
v___x_567_ = 0;
v___x_568_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_a_564_, v___x_566_, v___f_565_, v___x_567_, v___x_567_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_array_push(v_fst_474_, v_a_569_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_530_);
lean_ctor_set(v___x_571_, 1, v___x_510_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_558_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_460_, v___x_574_);
v_i_460_ = v___x_575_;
v_b_461_ = v___x_573_;
goto _start;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v___x_558_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_510_);
lean_dec(v_fst_474_);
lean_dec_ref(v_fixedArgs_457_);
v_a_577_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_558_);
lean_dec(v_ref_550_);
lean_dec_ref(v___x_530_);
lean_dec(v___x_527_);
lean_dec_ref(v___x_510_);
lean_dec(v_fst_474_);
lean_dec_ref(v_fixedArgs_457_);
v_a_585_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_563_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_563_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v___x_558_);
lean_dec(v_ref_550_);
lean_dec(v_val_542_);
lean_dec_ref(v___x_530_);
lean_dec(v___x_527_);
lean_dec_ref(v___x_510_);
lean_dec(v_fst_474_);
lean_dec_ref(v_fixedArgs_457_);
v_a_593_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_559_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_559_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
}
}
v___jp_531_:
{
lean_object* v___x_533_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_510_);
lean_ctor_set(v___x_484_, 0, v___x_530_);
v___x_533_ = v___x_484_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_510_);
v___x_533_ = v_reuseFailAlloc_541_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_533_);
v___x_535_ = v___x_480_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_478_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_540_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_535_);
v___x_537_ = v___x_476_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_474_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object* v_fixedParamPerms_623_, lean_object* v_fixedArgs_624_, lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_sz_boxed_636_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_637_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_623_, v_fixedArgs_624_, v_as_625_, v_sz_boxed_636_, v_i_boxed_637_, v_b_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_as_625_);
lean_dec_ref(v_fixedParamPerms_623_);
return v_res_638_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object* v_upperBound_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_termMeasures_654_, lean_object* v_names_655_, lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_a_666_; uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v_a_656_, v_upperBound_651_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v_a_656_);
lean_dec_ref(v___x_653_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_b_657_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
v___x_673_ = lean_box(0);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_box(0);
v___x_676_ = lean_array_fget_borrowed(v___x_652_, v_a_656_);
lean_inc(v___x_676_);
lean_inc_ref(v___x_653_);
v___x_677_ = l_Lean_Meta_isExprDefEqGuarded(v___x_653_, v___x_676_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; uint8_t v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = lean_unbox(v_a_678_);
lean_dec(v_a_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v_ref_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_680_ = lean_array_get_borrowed(v___x_672_, v_termMeasures_654_, v_a_656_);
v_ref_681_ = lean_ctor_get(v___x_680_, 0);
v___x_682_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
v___x_683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
v___x_684_ = lean_array_get_borrowed(v___x_673_, v_names_655_, v___x_674_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_MessageData_ofName(v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_682_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_inc_ref(v___x_653_);
v___x_690_ = l_Lean_indentExpr(v___x_653_);
v___x_691_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_689_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
v___x_695_ = lean_array_get_borrowed(v___x_673_, v_names_655_, v_a_656_);
lean_inc(v___x_695_);
v___x_696_ = l_Lean_MessageData_ofName(v___x_695_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_687_);
lean_inc(v___x_676_);
v___x_699_ = l_Lean_indentExpr(v___x_676_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_691_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_693_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_681_, v___x_704_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_dec_ref_known(v___x_705_, 1);
v_a_666_ = v___x_675_;
goto v___jp_665_;
}
else
{
lean_dec(v_a_656_);
lean_dec_ref(v___x_653_);
return v___x_705_;
}
}
else
{
v_a_666_ = v___x_675_;
goto v___jp_665_;
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_656_);
lean_dec_ref(v___x_653_);
v_a_706_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_677_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_677_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_a_656_, v___x_667_);
lean_dec(v_a_656_);
v_a_656_ = v___x_668_;
v_b_657_ = v_a_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object* v_upperBound_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v_termMeasures_717_, lean_object* v_names_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_714_, v___x_715_, v___x_716_, v_termMeasures_717_, v_names_718_, v_a_719_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_names_718_);
lean_dec_ref(v_termMeasures_717_);
lean_dec_ref(v___x_715_);
lean_dec(v_upperBound_714_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* v_names_733_, lean_object* v_fixedParamPerms_734_, lean_object* v_fixedArgs_735_, lean_object* v_arities_736_, lean_object* v_termMeasures_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_codomains_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; size_t v_sz_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_745_ = l_Lean_instInhabitedExpr;
v___x_746_ = lean_unsigned_to_nat(0u);
v_codomains_747_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__0));
v___x_748_ = lean_array_get_size(v_names_733_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__1));
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
v___x_751_ = lean_array_get_size(v_arities_736_);
v___x_752_ = l_Array_toSubarray___redArg(v_arities_736_, v___x_746_, v___x_751_);
v___x_753_ = lean_array_get_size(v_termMeasures_737_);
lean_inc_ref(v_termMeasures_737_);
v___x_754_ = l_Array_toSubarray___redArg(v_termMeasures_737_, v___x_746_, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_750_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_codomains_747_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v_sz_758_ = lean_array_size(v_names_733_);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_734_, v_fixedArgs_735_, v_names_733_, v_sz_758_, v___x_759_, v___x_757_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v_fst_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v_fst_762_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_fst_762_);
lean_dec(v_a_761_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_array_get_size(v_fst_762_);
v___x_765_ = lean_array_get(v___x_745_, v_fst_762_, v___x_746_);
v___x_766_ = lean_box(0);
lean_inc(v___x_765_);
v___x_767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v___x_764_, v_fst_762_, v___x_765_, v_termMeasures_737_, v_names_733_, v___x_763_, v___x_766_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec_ref(v_termMeasures_737_);
lean_dec(v_fst_762_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_775_);
v___x_769_ = v___x_767_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_dec(v___x_767_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_765_);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_765_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_765_);
v_a_776_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_767_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_termMeasures_737_);
v_a_784_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_760_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_760_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* v_names_792_, lean_object* v_fixedParamPerms_793_, lean_object* v_fixedArgs_794_, lean_object* v_arities_795_, lean_object* v_termMeasures_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Elab_WF_checkCodomains(v_names_792_, v_fixedParamPerms_793_, v_fixedArgs_794_, v_arities_795_, v_termMeasures_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec_ref(v_fixedParamPerms_793_);
lean_dec_ref(v_names_792_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object* v_00_u03b1_805_, lean_object* v_ref_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_806_, v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object* v_00_u03b1_816_, lean_object* v_ref_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(v_00_u03b1_816_, v_ref_817_, v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v_ref_817_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object* v_upperBound_827_, lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v_termMeasures_830_, lean_object* v_names_831_, lean_object* v_inst_832_, lean_object* v_R_833_, lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_c_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_827_, v___x_828_, v___x_829_, v_termMeasures_830_, v_names_831_, v_a_834_, v_b_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_845_ = _args[0];
lean_object* v___x_846_ = _args[1];
lean_object* v___x_847_ = _args[2];
lean_object* v_termMeasures_848_ = _args[3];
lean_object* v_names_849_ = _args[4];
lean_object* v_inst_850_ = _args[5];
lean_object* v_R_851_ = _args[6];
lean_object* v_a_852_ = _args[7];
lean_object* v_b_853_ = _args[8];
lean_object* v_c_854_ = _args[9];
lean_object* v___y_855_ = _args[10];
lean_object* v___y_856_ = _args[11];
lean_object* v___y_857_ = _args[12];
lean_object* v___y_858_ = _args[13];
lean_object* v___y_859_ = _args[14];
lean_object* v___y_860_ = _args[15];
lean_object* v___y_861_ = _args[16];
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(v_upperBound_845_, v___x_846_, v___x_847_, v_termMeasures_848_, v_names_849_, v_inst_850_, v_R_851_, v_a_852_, v_b_853_, v_c_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v_names_849_);
lean_dec_ref(v_termMeasures_848_);
lean_dec_ref(v___x_846_);
lean_dec(v_upperBound_845_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object* v_00_u03b1_863_, lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object* v_00_u03b1_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(v_00_u03b1_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object* v_msgData_883_, lean_object* v_macroStack_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_883_, v_macroStack_884_, v___y_889_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_893_, lean_object* v_macroStack_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_893_, v_macroStack_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object* v_e_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Expr_hasMVar(v_e_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_e_903_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v_mctx_909_; lean_object* v___x_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_913_; lean_object* v_cache_914_; lean_object* v_zetaDeltaFVarIds_915_; lean_object* v_postponed_916_; lean_object* v_diag_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_926_; 
v___x_908_ = lean_st_ref_get(v___y_904_);
v_mctx_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_mctx_909_);
lean_dec(v___x_908_);
v___x_910_ = l_Lean_instantiateMVarsCore(v_mctx_909_, v_e_903_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_910_);
v___x_913_ = lean_st_ref_take(v___y_904_);
v_cache_914_ = lean_ctor_get(v___x_913_, 1);
v_zetaDeltaFVarIds_915_ = lean_ctor_get(v___x_913_, 2);
v_postponed_916_ = lean_ctor_get(v___x_913_, 3);
v_diag_917_ = lean_ctor_get(v___x_913_, 4);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_927_);
v___x_919_ = v___x_913_;
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_diag_917_);
lean_inc(v_postponed_916_);
lean_inc(v_zetaDeltaFVarIds_915_);
lean_inc(v_cache_914_);
lean_dec(v___x_913_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_snd_912_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_snd_912_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_cache_914_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_zetaDeltaFVarIds_915_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_postponed_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_diag_917_);
v___x_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_st_ref_put(v___y_904_, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_fst_911_);
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object* v_e_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_928_, v___y_929_);
lean_dec(v___y_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object* v_e_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_932_, v___y_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object* v_e_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(v_e_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object* v_fixedParamPerms_950_, lean_object* v_fixedArgs_951_, size_t v_sz_952_, size_t v_i_953_, lean_object* v_bs_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_fixedArgs_951_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_bs_954_);
return v___x_961_;
}
else
{
lean_object* v_v_962_; lean_object* v_perms_963_; lean_object* v_fn_964_; lean_object* v___x_965_; lean_object* v_bs_x27_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_v_962_ = lean_array_uget_borrowed(v_bs_954_, v_i_953_);
v_perms_963_ = lean_ctor_get(v_fixedParamPerms_950_, 1);
v_fn_964_ = lean_ctor_get(v_v_962_, 1);
lean_inc_ref(v_fn_964_);
v___x_965_ = lean_unsigned_to_nat(0u);
v_bs_x27_966_ = lean_array_uset(v_bs_954_, v_i_953_, v___x_965_);
v___x_967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_968_ = lean_usize_to_nat(v_i_953_);
v___x_969_ = lean_array_get_borrowed(v___x_967_, v_perms_963_, v___x_968_);
lean_dec(v___x_968_);
lean_inc_ref(v_fixedArgs_951_);
lean_inc(v___x_969_);
v___x_970_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_969_, v_fn_964_, v_fixedArgs_951_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_953_, v___x_972_);
v___x_974_ = lean_array_uset(v_bs_x27_966_, v_i_953_, v_a_971_);
v_i_953_ = v___x_973_;
v_bs_954_ = v___x_974_;
goto _start;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_bs_x27_966_);
lean_dec_ref(v_fixedArgs_951_);
v_a_976_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_970_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object* v_fixedParamPerms_984_, lean_object* v_fixedArgs_985_, lean_object* v_sz_986_, lean_object* v_i_987_, lean_object* v_bs_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
size_t v_sz_boxed_994_; size_t v_i_boxed_995_; lean_object* v_res_996_; 
v_sz_boxed_994_ = lean_unbox_usize(v_sz_986_);
lean_dec(v_sz_986_);
v_i_boxed_995_ = lean_unbox_usize(v_i_987_);
lean_dec(v_i_987_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_984_, v_fixedArgs_985_, v_sz_boxed_994_, v_i_boxed_995_, v_bs_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_fixedParamPerms_984_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object* v_argType_1003_, lean_object* v_argsPacker_1004_, lean_object* v_declNames_1005_, lean_object* v_fixedParamPerms_1006_, lean_object* v_fixedArgs_1007_, lean_object* v_termMeasures_1008_, lean_object* v_k_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
lean_inc_ref(v_argType_1003_);
v___x_1017_ = l_Lean_Meta_getLevel(v_argType_1003_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
lean_inc_ref(v_argsPacker_1004_);
v___x_1019_ = l_Lean_Meta_ArgsPacker_arities(v_argsPacker_1004_);
lean_inc_ref(v_termMeasures_1008_);
lean_inc_ref(v_fixedArgs_1007_);
v___x_1020_ = l_Lean_Elab_WF_checkCodomains(v_declNames_1005_, v_fixedParamPerms_1006_, v_fixedArgs_1007_, v___x_1019_, v_termMeasures_1008_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_n(v_a_1021_, 2);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Meta_getLevel(v_a_1021_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; size_t v_sz_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_sz_1024_ = lean_array_size(v_termMeasures_1008_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1006_, v_fixedArgs_1007_, v_sz_1024_, v___x_1025_, v_termMeasures_1008_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_1004_, v_a_1027_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v_a_1027_);
lean_dec_ref(v_argsPacker_1004_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1));
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1023_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_inc_ref(v___x_1032_);
v___x_1033_ = l_Lean_Expr_const___override(v___x_1030_, v___x_1032_);
lean_inc(v_a_1021_);
v___x_1034_ = l_Lean_Expr_app___override(v___x_1033_, v_a_1021_);
v___x_1035_ = lean_box(0);
v___x_1036_ = l_Lean_Meta_synthInstance(v___x_1034_, v___x_1035_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3));
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1018_);
lean_ctor_set(v___x_1039_, 1, v___x_1032_);
v___x_1040_ = l_Lean_Expr_const___override(v___x_1038_, v___x_1039_);
v___x_1041_ = l_Lean_mkApp4(v___x_1040_, v_argType_1003_, v_a_1021_, v_a_1029_, v_a_1037_);
v___x_1042_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v___x_1041_, v___y_1013_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = lean_apply_8(v_k_1009_, v_a_1043_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, lean_box(0));
return v___x_1044_;
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref_known(v___x_1032_, 2);
lean_dec(v_a_1029_);
lean_dec(v_a_1021_);
lean_dec(v_a_1018_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_argType_1003_);
v_a_1045_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1036_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1036_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1023_);
lean_dec(v_a_1021_);
lean_dec(v_a_1018_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_argType_1003_);
v_a_1053_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1028_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1028_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1023_);
lean_dec(v_a_1021_);
lean_dec(v_a_1018_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_argsPacker_1004_);
lean_dec_ref(v_argType_1003_);
v_a_1061_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1026_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1026_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_1021_);
lean_dec(v_a_1018_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_termMeasures_1008_);
lean_dec_ref(v_fixedArgs_1007_);
lean_dec_ref(v_argsPacker_1004_);
lean_dec_ref(v_argType_1003_);
v_a_1069_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1022_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1022_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v_a_1018_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_termMeasures_1008_);
lean_dec_ref(v_fixedArgs_1007_);
lean_dec_ref(v_argsPacker_1004_);
lean_dec_ref(v_argType_1003_);
v_a_1077_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1020_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1020_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_termMeasures_1008_);
lean_dec_ref(v_fixedArgs_1007_);
lean_dec_ref(v_argsPacker_1004_);
lean_dec_ref(v_argType_1003_);
v_a_1085_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1017_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1017_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object* v_argType_1093_, lean_object* v_argsPacker_1094_, lean_object* v_declNames_1095_, lean_object* v_fixedParamPerms_1096_, lean_object* v_fixedArgs_1097_, lean_object* v_termMeasures_1098_, lean_object* v_k_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(v_argType_1093_, v_argsPacker_1094_, v_declNames_1095_, v_fixedParamPerms_1096_, v_fixedArgs_1097_, v_termMeasures_1098_, v_k_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v_fixedParamPerms_1096_);
lean_dec_ref(v_declNames_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object* v_declNames_1108_, lean_object* v_unaryPreDefName_1109_, lean_object* v_fixedParamPerms_1110_, lean_object* v_fixedArgs_1111_, lean_object* v_argsPacker_1112_, lean_object* v_argType_1113_, lean_object* v_termMeasures_1114_, lean_object* v_k_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1123_, 0, v_argType_1113_);
lean_closure_set(v___f_1123_, 1, v_argsPacker_1112_);
lean_closure_set(v___f_1123_, 2, v_declNames_1108_);
lean_closure_set(v___f_1123_, 3, v_fixedParamPerms_1110_);
lean_closure_set(v___f_1123_, 4, v_fixedArgs_1111_);
lean_closure_set(v___f_1123_, 5, v_termMeasures_1114_);
lean_closure_set(v___f_1123_, 6, v_k_1115_);
v___x_1124_ = l_Lean_Elab_Term_withDeclName___redArg(v_unaryPreDefName_1109_, v___f_1123_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object* v_declNames_1125_, lean_object* v_unaryPreDefName_1126_, lean_object* v_fixedParamPerms_1127_, lean_object* v_fixedArgs_1128_, lean_object* v_argsPacker_1129_, lean_object* v_argType_1130_, lean_object* v_termMeasures_1131_, lean_object* v_k_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1125_, v_unaryPreDefName_1126_, v_fixedParamPerms_1127_, v_fixedArgs_1128_, v_argsPacker_1129_, v_argType_1130_, v_termMeasures_1131_, v_k_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* v_00_u03b1_1141_, lean_object* v_declNames_1142_, lean_object* v_unaryPreDefName_1143_, lean_object* v_fixedParamPerms_1144_, lean_object* v_fixedArgs_1145_, lean_object* v_argsPacker_1146_, lean_object* v_argType_1147_, lean_object* v_termMeasures_1148_, lean_object* v_k_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1142_, v_unaryPreDefName_1143_, v_fixedParamPerms_1144_, v_fixedArgs_1145_, v_argsPacker_1146_, v_argType_1147_, v_termMeasures_1148_, v_k_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_declNames_1159_, lean_object* v_unaryPreDefName_1160_, lean_object* v_fixedParamPerms_1161_, lean_object* v_fixedArgs_1162_, lean_object* v_argsPacker_1163_, lean_object* v_argType_1164_, lean_object* v_termMeasures_1165_, lean_object* v_k_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Elab_WF_elabWFRel(v_00_u03b1_1158_, v_declNames_1159_, v_unaryPreDefName_1160_, v_fixedParamPerms_1161_, v_fixedArgs_1162_, v_argsPacker_1163_, v_argType_1164_, v_termMeasures_1165_, v_k_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object* v_fixedParamPerms_1175_, lean_object* v_fixedArgs_1176_, lean_object* v_as_1177_, size_t v_sz_1178_, size_t v_i_1179_, lean_object* v_bs_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1175_, v_fixedArgs_1176_, v_sz_1178_, v_i_1179_, v_bs_1180_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object* v_fixedParamPerms_1189_, lean_object* v_fixedArgs_1190_, lean_object* v_as_1191_, lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
size_t v_sz_boxed_1202_; size_t v_i_boxed_1203_; lean_object* v_res_1204_; 
v_sz_boxed_1202_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1203_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(v_fixedParamPerms_1189_, v_fixedArgs_1190_, v_as_1191_, v_sz_boxed_1202_, v_i_boxed_1203_, v_bs_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v_as_1191_);
lean_dec_ref(v_fixedParamPerms_1189_);
return v_res_1204_;
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
