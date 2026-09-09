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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v___x_201_; lean_object* v_toCold_202_; lean_object* v_mctx_203_; lean_object* v_lctx_204_; lean_object* v_options_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v___x_201_ = lean_st_ref_get(v___y_195_);
v_toCold_202_ = lean_ctor_get(v___y_196_, 0);
v_mctx_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_mctx_203_);
lean_dec(v___x_201_);
v_lctx_204_ = lean_ctor_get(v___y_194_, 2);
v_options_205_ = lean_ctor_get(v_toCold_202_, 2);
lean_inc_ref(v_options_205_);
lean_inc_ref(v_lctx_204_);
v___x_206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_206_, 0, v_env_200_);
lean_ctor_set(v___x_206_, 1, v_mctx_203_);
lean_ctor_set(v___x_206_, 2, v_lctx_204_);
lean_ctor_set(v___x_206_, 3, v_options_205_);
v___x_207_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_msgData_193_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object* v_msgData_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object* v_opts_216_, lean_object* v_opt_217_){
_start:
{
lean_object* v_name_218_; lean_object* v_defValue_219_; lean_object* v_map_220_; lean_object* v___x_221_; 
v_name_218_ = lean_ctor_get(v_opt_217_, 0);
v_defValue_219_ = lean_ctor_get(v_opt_217_, 1);
v_map_220_ = lean_ctor_get(v_opts_216_, 0);
v___x_221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_220_, v_name_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = lean_unbox(v_defValue_219_);
return v___x_222_;
}
else
{
lean_object* v_val_223_; 
v_val_223_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_221_, 1);
if (lean_obj_tag(v_val_223_) == 1)
{
uint8_t v_v_224_; 
v_v_224_ = lean_ctor_get_uint8(v_val_223_, 0);
lean_dec_ref_known(v_val_223_, 0);
return v_v_224_;
}
else
{
uint8_t v___x_225_; 
lean_dec(v_val_223_);
v___x_225_ = lean_unbox(v_defValue_219_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object* v_opts_226_, lean_object* v_opt_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_226_, v_opt_227_);
lean_dec_ref(v_opt_227_);
lean_dec_ref(v_opts_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_box(1);
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2));
v___x_236_ = l_Lean_MessageData_ofFormat(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
return v_x_237_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_262_; 
v_head_239_ = lean_ctor_get(v_x_238_, 0);
v_tail_240_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_262_ == 0)
{
v___x_242_ = v_x_238_;
v_isShared_243_ = v_isSharedCheck_262_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_tail_240_);
lean_inc(v_head_239_);
lean_dec(v_x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_262_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_before_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_260_; 
v_before_244_ = lean_ctor_get(v_head_239_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_head_239_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v_head_239_, 1);
lean_dec(v_unused_261_);
v___x_246_ = v_head_239_;
v_isShared_247_ = v_isSharedCheck_260_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_before_244_);
lean_dec(v_head_239_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_260_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 7);
lean_ctor_set(v___x_246_, 1, v___x_248_);
lean_ctor_set(v___x_246_, 0, v_x_237_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_x_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_259_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 7);
lean_ctor_set(v___x_242_, 1, v___x_251_);
lean_ctor_set(v___x_242_, 0, v___x_250_);
v___x_253_ = v___x_242_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_258_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = l_Lean_MessageData_ofSyntax(v_before_244_);
v___x_255_ = l_Lean_indentD(v___x_254_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v_x_237_ = v___x_256_;
v_x_238_ = v_tail_240_;
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
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1));
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object* v_msgData_268_, lean_object* v_macroStack_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_toCold_272_; lean_object* v_options_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_toCold_272_ = lean_ctor_get(v___y_270_, 0);
v_options_273_ = lean_ctor_get(v_toCold_272_, 2);
v___x_274_ = l_Lean_Elab_pp_macroStack;
v___x_275_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_options_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_macroStack_269_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_msgData_268_);
return v___x_276_;
}
else
{
if (lean_obj_tag(v_macroStack_269_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_msgData_268_);
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_after_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_294_; 
v_head_278_ = lean_ctor_get(v_macroStack_269_, 0);
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
lean_ctor_set(v___x_281_, 0, v_msgData_268_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_msgData_268_);
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
v___x_291_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(v_msgData_290_, v_macroStack_269_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_296_, lean_object* v_macroStack_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_296_, v_macroStack_297_, v___y_298_);
lean_dec_ref(v___y_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v_macroStack_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_ref_309_ = lean_ctor_get(v___y_306_, 2);
v___x_310_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msg_301_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_310_);
v_macroStack_312_ = lean_ctor_get(v___y_302_, 1);
v___x_313_ = l_Lean_Elab_getBetterRef(v_ref_309_, v_macroStack_312_);
lean_inc(v_macroStack_312_);
v___x_314_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_a_311_, v_macroStack_312_, v___y_306_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_313_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 1);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object* v_ref_333_, lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_toCold_342_; lean_object* v_currRecDepth_343_; lean_object* v_ref_344_; uint8_t v_diag_345_; uint8_t v_suppressElabErrors_346_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_toCold_342_ = lean_ctor_get(v___y_339_, 0);
v_currRecDepth_343_ = lean_ctor_get(v___y_339_, 1);
v_ref_344_ = lean_ctor_get(v___y_339_, 2);
v_diag_345_ = lean_ctor_get_uint8(v___y_339_, sizeof(void*)*3);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_339_, sizeof(void*)*3 + 1);
v_ref_347_ = l_Lean_replaceRef(v_ref_333_, v_ref_344_);
lean_inc(v_currRecDepth_343_);
lean_inc_ref(v_toCold_342_);
v___x_348_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_348_, 0, v_toCold_342_);
lean_ctor_set(v___x_348_, 1, v_currRecDepth_343_);
lean_ctor_set(v___x_348_, 2, v_ref_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*3, v_diag_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*3 + 1, v_suppressElabErrors_346_);
v___x_349_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___x_348_, v___y_340_);
lean_dec_ref_known(v___x_348_, 3);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object* v_ref_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v_ref_350_);
return v_res_359_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2));
v___x_364_ = lean_unsigned_to_nat(6u);
v___x_365_ = lean_unsigned_to_nat(33u);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1));
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0));
v___x_368_ = l_mkPanicMessageWithDecl(v___x_367_, v___x_366_, v___x_365_, v___x_364_, v___x_363_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13));
v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_ref_389_, lean_object* v_xs_390_, lean_object* v_codomain_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_array_get_size(v_xs_390_);
v___x_400_ = lean_nat_dec_eq(v___x_399_, v___x_386_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v_codomain_391_);
lean_dec_ref(v_xs_390_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
v___x_401_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
v___x_402_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(v___x_401_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_402_;
}
else
{
size_t v_sz_403_; size_t v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_sz_403_ = lean_array_size(v_xs_390_);
v___x_404_ = ((size_t)0ULL);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_403_, v___x_404_, v_xs_390_);
v___x_406_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_405_, v_codomain_391_);
lean_dec_ref(v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_codomain_391_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
v___x_409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
v___x_410_ = l_Lean_MessageData_ofName(v_a_387_);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_indentExpr(v_a_388_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_408_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_389_, v___x_420_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v___x_421_, 0);
lean_dec(v_unused_429_);
v___x_423_ = v___x_421_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_dec(v___x_421_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v_codomain_391_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_codomain_391_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_codomain_391_);
v_a_430_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_421_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_421_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object* v___x_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_ref_441_, lean_object* v_xs_442_, lean_object* v_codomain_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_438_, v_a_439_, v_a_440_, v_ref_441_, v_xs_442_, v_codomain_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v_ref_441_);
lean_dec(v___x_438_);
return v_res_451_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0(void){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Array_instInhabited(lean_box(0));
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object* v_fixedParamPerms_453_, lean_object* v_fixedArgs_454_, lean_object* v_as_455_, size_t v_sz_456_, size_t v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec_ref(v_fixedArgs_454_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_b_458_);
return v___x_467_;
}
else
{
lean_object* v_snd_468_; lean_object* v_snd_469_; lean_object* v_snd_470_; lean_object* v_fst_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_618_; 
v_snd_468_ = lean_ctor_get(v_b_458_, 1);
lean_inc(v_snd_468_);
v_snd_469_ = lean_ctor_get(v_snd_468_, 1);
lean_inc(v_snd_469_);
v_snd_470_ = lean_ctor_get(v_snd_469_, 1);
lean_inc(v_snd_470_);
v_fst_471_ = lean_ctor_get(v_b_458_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_b_458_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_b_458_, 1);
lean_dec(v_unused_619_);
v___x_473_ = v_b_458_;
v_isShared_474_ = v_isSharedCheck_618_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_fst_471_);
lean_dec(v_b_458_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_618_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_fst_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_616_; 
v_fst_475_ = lean_ctor_get(v_snd_468_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_468_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v_snd_468_, 1);
lean_dec(v_unused_617_);
v___x_477_ = v_snd_468_;
v_isShared_478_ = v_isSharedCheck_616_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_fst_475_);
lean_dec(v_snd_468_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_616_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_fst_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_614_; 
v_fst_479_ = lean_ctor_get(v_snd_469_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_snd_469_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_snd_469_, 1);
lean_dec(v_unused_615_);
v___x_481_ = v_snd_469_;
v_isShared_482_ = v_isSharedCheck_614_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_fst_479_);
lean_dec(v_snd_469_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_614_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_array_483_; lean_object* v_start_484_; lean_object* v_stop_485_; uint8_t v___x_486_; 
v_array_483_ = lean_ctor_get(v_snd_470_, 0);
v_start_484_ = lean_ctor_get(v_snd_470_, 1);
v_stop_485_ = lean_ctor_get(v_snd_470_, 2);
v___x_486_ = lean_nat_dec_lt(v_start_484_, v_stop_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_fixedArgs_454_);
if (v_isShared_482_ == 0)
{
v___x_488_ = v___x_481_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_470_);
v___x_488_ = v_reuseFailAlloc_496_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_488_);
v___x_490_ = v___x_477_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_fst_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_495_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_490_);
v___x_492_ = v___x_473_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_494_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_610_; 
lean_inc(v_stop_485_);
lean_inc(v_start_484_);
lean_inc_ref(v_array_483_);
v_isSharedCheck_610_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; lean_object* v_unused_613_; 
v_unused_611_ = lean_ctor_get(v_snd_470_, 2);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_snd_470_, 1);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_snd_470_, 0);
lean_dec(v_unused_613_);
v___x_498_ = v_snd_470_;
v_isShared_499_ = v_isSharedCheck_610_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_snd_470_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_610_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_array_500_; lean_object* v_start_501_; lean_object* v_stop_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v_array_500_ = lean_ctor_get(v_fst_479_, 0);
v_start_501_ = lean_ctor_get(v_fst_479_, 1);
v_stop_502_ = lean_ctor_get(v_fst_479_, 2);
v___x_503_ = lean_array_fget(v_array_483_, v_start_484_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_start_484_, v___x_504_);
lean_dec(v_start_484_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_505_);
v___x_507_ = v___x_498_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_array_483_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_stop_485_);
v___x_507_ = v_reuseFailAlloc_609_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
uint8_t v___x_508_; 
v___x_508_ = lean_nat_dec_lt(v_start_501_, v_stop_502_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v___x_503_);
lean_dec_ref(v_fixedArgs_454_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_507_);
v___x_510_ = v___x_481_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_fst_479_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_507_);
v___x_510_ = v_reuseFailAlloc_518_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_510_);
v___x_512_ = v___x_477_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_475_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_517_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_512_);
v___x_514_ = v___x_473_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_605_; 
lean_inc(v_stop_502_);
lean_inc(v_start_501_);
lean_inc_ref(v_array_500_);
v_isSharedCheck_605_ = !lean_is_exclusive(v_fst_479_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_606_ = lean_ctor_get(v_fst_479_, 2);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_fst_479_, 1);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_fst_479_, 0);
lean_dec(v_unused_608_);
v___x_520_ = v_fst_479_;
v_isShared_521_ = v_isSharedCheck_605_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_fst_479_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_605_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_next_522_; lean_object* v_upperBound_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v_next_522_ = lean_ctor_get(v_fst_475_, 0);
lean_inc(v_next_522_);
v_upperBound_523_ = lean_ctor_get(v_fst_475_, 1);
v___x_524_ = lean_array_fget(v_array_500_, v_start_501_);
v___x_525_ = lean_nat_add(v_start_501_, v___x_504_);
lean_dec(v_start_501_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_525_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_array_500_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_stop_502_);
v___x_527_ = v_reuseFailAlloc_604_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
if (lean_obj_tag(v_next_522_) == 0)
{
lean_dec(v___x_524_);
lean_dec(v___x_503_);
lean_dec_ref(v_fixedArgs_454_);
goto v___jp_528_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_603_; 
v_val_539_ = lean_ctor_get(v_next_522_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_next_522_);
if (v_isSharedCheck_603_ == 0)
{
v___x_541_ = v_next_522_;
v_isShared_542_ = v_isSharedCheck_603_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v_next_522_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_603_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint8_t v___x_543_; 
v___x_543_ = lean_nat_dec_lt(v_val_539_, v_upperBound_523_);
if (v___x_543_ == 0)
{
lean_del_object(v___x_541_);
lean_dec(v_val_539_);
lean_dec(v___x_524_);
lean_dec(v___x_503_);
lean_dec_ref(v_fixedArgs_454_);
goto v___jp_528_;
}
else
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_600_; 
lean_inc(v_upperBound_523_);
lean_del_object(v___x_481_);
lean_del_object(v___x_477_);
lean_del_object(v___x_473_);
v_isSharedCheck_600_ = !lean_is_exclusive(v_fst_475_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_601_ = lean_ctor_get(v_fst_475_, 1);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_fst_475_, 0);
lean_dec(v_unused_602_);
v___x_545_ = v_fst_475_;
v_isShared_546_ = v_isSharedCheck_600_;
goto v_resetjp_544_;
}
else
{
lean_dec(v_fst_475_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_600_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_ref_547_; lean_object* v_fn_548_; lean_object* v___x_549_; 
v_ref_547_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_ref_547_);
v_fn_548_ = lean_ctor_get(v___x_503_, 1);
lean_inc_ref(v_fn_548_);
lean_dec(v___x_503_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
v___x_549_ = lean_infer_type(v_fn_548_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v_perms_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v_perms_551_ = lean_ctor_get(v_fixedParamPerms_453_, 1);
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_553_ = lean_array_get_borrowed(v___x_552_, v_perms_551_, v_val_539_);
lean_inc_ref(v_fixedArgs_454_);
lean_inc(v___x_553_);
v___x_554_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_553_, v_a_550_, v_fixedArgs_454_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v_a_556_; lean_object* v___f_557_; lean_object* v___x_559_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc_n(v_a_555_, 2);
lean_dec_ref_known(v___x_554_, 1);
v_a_556_ = lean_array_uget_borrowed(v_as_455_, v_i_457_);
lean_inc(v_a_556_);
lean_inc(v___x_524_);
v___f_557_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(v___f_557_, 0, v___x_524_);
lean_closure_set(v___f_557_, 1, v_a_556_);
lean_closure_set(v___f_557_, 2, v_a_555_);
lean_closure_set(v___f_557_, 3, v_ref_547_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_524_);
v___x_559_ = v___x_541_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_524_);
v___x_559_ = v_reuseFailAlloc_583_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_560_ = 0;
v___x_561_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_a_555_, v___x_559_, v___f_557_, v___x_560_, v___x_560_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = lean_nat_add(v_val_539_, v___x_504_);
lean_dec(v_val_539_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_564_);
v___x_566_ = v___x_545_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_upperBound_523_);
v___x_566_ = v_reuseFailAlloc_574_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; 
v___x_567_ = lean_array_push(v_fst_471_, v_a_562_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_527_);
lean_ctor_set(v___x_568_, 1, v___x_507_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_567_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_457_, v___x_571_);
v_i_457_ = v___x_572_;
v_b_458_ = v___x_570_;
goto _start;
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_del_object(v___x_545_);
lean_dec(v_val_539_);
lean_dec_ref(v___x_527_);
lean_dec(v_upperBound_523_);
lean_dec_ref(v___x_507_);
lean_dec(v_fst_471_);
lean_dec_ref(v_fixedArgs_454_);
v_a_575_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_561_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_561_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_ref_547_);
lean_del_object(v___x_545_);
lean_del_object(v___x_541_);
lean_dec(v_val_539_);
lean_dec_ref(v___x_527_);
lean_dec(v___x_524_);
lean_dec(v_upperBound_523_);
lean_dec_ref(v___x_507_);
lean_dec(v_fst_471_);
lean_dec_ref(v_fixedArgs_454_);
v_a_584_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_554_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_554_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_ref_547_);
lean_del_object(v___x_545_);
lean_del_object(v___x_541_);
lean_dec(v_val_539_);
lean_dec_ref(v___x_527_);
lean_dec(v___x_524_);
lean_dec(v_upperBound_523_);
lean_dec_ref(v___x_507_);
lean_dec(v_fst_471_);
lean_dec_ref(v_fixedArgs_454_);
v_a_592_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_549_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_549_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
}
v___jp_528_:
{
lean_object* v___x_530_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_507_);
lean_ctor_set(v___x_481_, 0, v___x_527_);
v___x_530_ = v___x_481_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_507_);
v___x_530_ = v_reuseFailAlloc_538_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_530_);
v___x_532_ = v___x_477_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_fst_475_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_537_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_532_);
v___x_534_ = v___x_473_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object* v_fixedParamPerms_620_, lean_object* v_fixedArgs_621_, lean_object* v_as_622_, lean_object* v_sz_623_, lean_object* v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
size_t v_sz_boxed_633_; size_t v_i_boxed_634_; lean_object* v_res_635_; 
v_sz_boxed_633_ = lean_unbox_usize(v_sz_623_);
lean_dec(v_sz_623_);
v_i_boxed_634_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_620_, v_fixedArgs_621_, v_as_622_, v_sz_boxed_633_, v_i_boxed_634_, v_b_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v_as_622_);
lean_dec_ref(v_fixedParamPerms_620_);
return v_res_635_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0));
v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object* v_upperBound_648_, lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v_termMeasures_651_, lean_object* v_names_652_, lean_object* v_a_653_, lean_object* v_b_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_a_663_; uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_lt(v_a_653_, v_upperBound_648_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v_a_653_);
lean_dec_ref(v___x_650_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_b_654_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_array_fget_borrowed(v___x_649_, v_a_653_);
lean_inc(v___x_669_);
lean_inc_ref(v___x_650_);
v___x_670_ = l_Lean_Meta_isExprDefEqGuarded(v___x_650_, v___x_669_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_box(0);
v___x_673_ = lean_unbox(v_a_671_);
lean_dec(v_a_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_ref_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_674_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
v___x_675_ = lean_array_get_borrowed(v___x_674_, v_termMeasures_651_, v_a_653_);
v_ref_676_ = lean_ctor_get(v___x_675_, 0);
v___x_677_ = lean_box(0);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
v___x_680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
v___x_681_ = lean_array_get_borrowed(v___x_677_, v_names_652_, v___x_678_);
lean_inc(v___x_681_);
v___x_682_ = l_Lean_MessageData_ofName(v___x_681_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_679_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
lean_inc_ref(v___x_650_);
v___x_687_ = l_Lean_indentExpr(v___x_650_);
v___x_688_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_686_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
v___x_692_ = lean_array_get_borrowed(v___x_677_, v_names_652_, v_a_653_);
lean_inc(v___x_692_);
v___x_693_ = l_Lean_MessageData_ofName(v___x_692_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_691_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_684_);
lean_inc(v___x_669_);
v___x_696_ = l_Lean_indentExpr(v___x_669_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_688_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_690_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_676_, v___x_701_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref_known(v___x_702_, 1);
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
else
{
lean_dec(v_a_653_);
lean_dec_ref(v___x_650_);
return v___x_702_;
}
}
else
{
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_a_653_);
lean_dec_ref(v___x_650_);
v_a_703_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_670_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_670_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_a_653_, v___x_664_);
lean_dec(v_a_653_);
v_a_653_ = v___x_665_;
v_b_654_ = v_a_663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object* v_upperBound_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v_termMeasures_714_, lean_object* v_names_715_, lean_object* v_a_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_711_, v___x_712_, v___x_713_, v_termMeasures_714_, v_names_715_, v_a_716_, v_b_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec_ref(v_names_715_);
lean_dec_ref(v_termMeasures_714_);
lean_dec_ref(v___x_712_);
lean_dec(v_upperBound_711_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* v_names_730_, lean_object* v_fixedParamPerms_731_, lean_object* v_fixedArgs_732_, lean_object* v_arities_733_, lean_object* v_termMeasures_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_codomains_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; size_t v_sz_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v_codomains_743_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__0));
v___x_744_ = lean_array_get_size(v_names_730_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__1));
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
v___x_747_ = lean_array_get_size(v_arities_733_);
v___x_748_ = l_Array_toSubarray___redArg(v_arities_733_, v___x_742_, v___x_747_);
v___x_749_ = lean_array_get_size(v_termMeasures_734_);
lean_inc_ref(v_termMeasures_734_);
v___x_750_ = l_Array_toSubarray___redArg(v_termMeasures_734_, v___x_742_, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_748_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_746_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_codomains_743_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v_sz_754_ = lean_array_size(v_names_730_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_731_, v_fixedArgs_732_, v_names_730_, v_sz_754_, v___x_755_, v___x_753_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v_fst_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v_fst_758_ = lean_ctor_get(v_a_757_, 0);
lean_inc(v_fst_758_);
lean_dec(v_a_757_);
v___x_759_ = l_Lean_instInhabitedExpr;
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_array_get_size(v_fst_758_);
v___x_762_ = lean_array_get(v___x_759_, v_fst_758_, v___x_742_);
v___x_763_ = lean_box(0);
lean_inc(v___x_762_);
v___x_764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v___x_761_, v_fst_758_, v___x_762_, v_termMeasures_734_, v_names_730_, v___x_760_, v___x_763_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec_ref(v_termMeasures_734_);
lean_dec(v_fst_758_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_772_);
v___x_766_ = v___x_764_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_dec(v___x_764_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_762_);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_762_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v___x_762_);
v_a_773_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_764_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_764_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_termMeasures_734_);
v_a_781_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_756_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_756_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* v_names_789_, lean_object* v_fixedParamPerms_790_, lean_object* v_fixedArgs_791_, lean_object* v_arities_792_, lean_object* v_termMeasures_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Elab_WF_checkCodomains(v_names_789_, v_fixedParamPerms_790_, v_fixedArgs_791_, v_arities_792_, v_termMeasures_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec_ref(v_fixedParamPerms_790_);
lean_dec_ref(v_names_789_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object* v_00_u03b1_802_, lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object* v_00_u03b1_813_, lean_object* v_ref_814_, lean_object* v_msg_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(v_00_u03b1_813_, v_ref_814_, v_msg_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v_ref_814_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object* v_upperBound_824_, lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v_termMeasures_827_, lean_object* v_names_828_, lean_object* v_inst_829_, lean_object* v_R_830_, lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v_c_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v_upperBound_824_, v___x_825_, v___x_826_, v_termMeasures_827_, v_names_828_, v_a_831_, v_b_832_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_842_ = _args[0];
lean_object* v___x_843_ = _args[1];
lean_object* v___x_844_ = _args[2];
lean_object* v_termMeasures_845_ = _args[3];
lean_object* v_names_846_ = _args[4];
lean_object* v_inst_847_ = _args[5];
lean_object* v_R_848_ = _args[6];
lean_object* v_a_849_ = _args[7];
lean_object* v_b_850_ = _args[8];
lean_object* v_c_851_ = _args[9];
lean_object* v___y_852_ = _args[10];
lean_object* v___y_853_ = _args[11];
lean_object* v___y_854_ = _args[12];
lean_object* v___y_855_ = _args[13];
lean_object* v___y_856_ = _args[14];
lean_object* v___y_857_ = _args[15];
lean_object* v___y_858_ = _args[16];
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(v_upperBound_842_, v___x_843_, v___x_844_, v_termMeasures_845_, v_names_846_, v_inst_847_, v_R_848_, v_a_849_, v_b_850_, v_c_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_names_846_);
lean_dec_ref(v_termMeasures_845_);
lean_dec_ref(v___x_843_);
lean_dec(v_upperBound_842_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object* v_00_u03b1_860_, lean_object* v_msg_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object* v_00_u03b1_870_, lean_object* v_msg_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(v_00_u03b1_870_, v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object* v_msgData_880_, lean_object* v_macroStack_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_880_, v_macroStack_881_, v___y_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_890_, lean_object* v_macroStack_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_890_, v_macroStack_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object* v_e_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Expr_hasMVar(v_e_900_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_e_900_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v_mctx_906_; lean_object* v___x_907_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_910_; lean_object* v_cache_911_; lean_object* v_zetaDeltaFVarIds_912_; lean_object* v_postponed_913_; lean_object* v_diag_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_923_; 
v___x_905_ = lean_st_ref_get(v___y_901_);
v_mctx_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_mctx_906_);
lean_dec(v___x_905_);
v___x_907_ = l_Lean_instantiateMVarsCore(v_mctx_906_, v_e_900_);
v_fst_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_fst_908_);
v_snd_909_ = lean_ctor_get(v___x_907_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v___x_907_);
v___x_910_ = lean_st_ref_take(v___y_901_);
v_cache_911_ = lean_ctor_get(v___x_910_, 1);
v_zetaDeltaFVarIds_912_ = lean_ctor_get(v___x_910_, 2);
v_postponed_913_ = lean_ctor_get(v___x_910_, 3);
v_diag_914_ = lean_ctor_get(v___x_910_, 4);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_910_, 0);
lean_dec(v_unused_924_);
v___x_916_ = v___x_910_;
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_diag_914_);
lean_inc(v_postponed_913_);
lean_inc(v_zetaDeltaFVarIds_912_);
lean_inc(v_cache_911_);
lean_dec(v___x_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_snd_909_);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_snd_909_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_cache_911_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_zetaDeltaFVarIds_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_postponed_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_diag_914_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_st_ref_put(v___y_901_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v_fst_908_);
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object* v_e_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_925_, v___y_926_);
lean_dec(v___y_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object* v_e_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v_e_929_, v___y_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(v_e_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object* v_fixedParamPerms_947_, lean_object* v_fixedArgs_948_, size_t v_sz_949_, size_t v_i_950_, lean_object* v_bs_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_950_, v_sz_949_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec_ref(v_fixedArgs_948_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_bs_951_);
return v___x_958_;
}
else
{
lean_object* v_v_959_; lean_object* v_perms_960_; lean_object* v_fn_961_; lean_object* v___x_962_; lean_object* v_bs_x27_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_v_959_ = lean_array_uget_borrowed(v_bs_951_, v_i_950_);
v_perms_960_ = lean_ctor_get(v_fixedParamPerms_947_, 1);
v_fn_961_ = lean_ctor_get(v_v_959_, 1);
lean_inc_ref(v_fn_961_);
v___x_962_ = lean_unsigned_to_nat(0u);
v_bs_x27_963_ = lean_array_uset(v_bs_951_, v_i_950_, v___x_962_);
v___x_964_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
v___x_965_ = lean_usize_to_nat(v_i_950_);
v___x_966_ = lean_array_get_borrowed(v___x_964_, v_perms_960_, v___x_965_);
lean_dec(v___x_965_);
lean_inc_ref(v_fixedArgs_948_);
lean_inc(v___x_966_);
v___x_967_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_966_, v_fn_961_, v_fixedArgs_948_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_950_, v___x_969_);
v___x_971_ = lean_array_uset(v_bs_x27_963_, v_i_950_, v_a_968_);
v_i_950_ = v___x_970_;
v_bs_951_ = v___x_971_;
goto _start;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_bs_x27_963_);
lean_dec_ref(v_fixedArgs_948_);
v_a_973_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_967_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_967_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object* v_fixedParamPerms_981_, lean_object* v_fixedArgs_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_bs_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
size_t v_sz_boxed_991_; size_t v_i_boxed_992_; lean_object* v_res_993_; 
v_sz_boxed_991_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_992_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_981_, v_fixedArgs_982_, v_sz_boxed_991_, v_i_boxed_992_, v_bs_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec_ref(v_fixedParamPerms_981_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object* v_argType_1000_, lean_object* v_argsPacker_1001_, lean_object* v_declNames_1002_, lean_object* v_fixedParamPerms_1003_, lean_object* v_fixedArgs_1004_, lean_object* v_termMeasures_1005_, lean_object* v_k_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
lean_inc_ref(v_argType_1000_);
v___x_1014_ = l_Lean_Meta_getLevel(v_argType_1000_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
lean_inc_ref(v_argsPacker_1001_);
v___x_1016_ = l_Lean_Meta_ArgsPacker_arities(v_argsPacker_1001_);
lean_inc_ref(v_termMeasures_1005_);
lean_inc_ref(v_fixedArgs_1004_);
v___x_1017_ = l_Lean_Elab_WF_checkCodomains(v_declNames_1002_, v_fixedParamPerms_1003_, v_fixedArgs_1004_, v___x_1016_, v_termMeasures_1005_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_n(v_a_1018_, 2);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l_Lean_Meta_getLevel(v_a_1018_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; size_t v_sz_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v_sz_1021_ = lean_array_size(v_termMeasures_1005_);
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1003_, v_fixedArgs_1004_, v_sz_1021_, v___x_1022_, v_termMeasures_1005_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_1001_, v_a_1024_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v_a_1024_);
lean_dec_ref(v_argsPacker_1001_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1));
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1020_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_inc_ref(v___x_1029_);
v___x_1030_ = l_Lean_Expr_const___override(v___x_1027_, v___x_1029_);
lean_inc(v_a_1018_);
v___x_1031_ = l_Lean_Expr_app___override(v___x_1030_, v_a_1018_);
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Lean_Meta_synthInstance(v___x_1031_, v___x_1032_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3));
v___x_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_a_1015_);
lean_ctor_set(v___x_1036_, 1, v___x_1029_);
v___x_1037_ = l_Lean_Expr_const___override(v___x_1035_, v___x_1036_);
v___x_1038_ = l_Lean_mkApp4(v___x_1037_, v_argType_1000_, v_a_1018_, v_a_1026_, v_a_1034_);
v___x_1039_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v___x_1038_, v___y_1010_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_apply_8(v_k_1006_, v_a_1040_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1041_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref_known(v___x_1029_, 2);
lean_dec(v_a_1026_);
lean_dec(v_a_1018_);
lean_dec(v_a_1015_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_argType_1000_);
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1033_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1020_);
lean_dec(v_a_1018_);
lean_dec(v_a_1015_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_argType_1000_);
v_a_1050_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1025_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1025_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_a_1020_);
lean_dec(v_a_1018_);
lean_dec(v_a_1015_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_argsPacker_1001_);
lean_dec_ref(v_argType_1000_);
v_a_1058_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1023_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1023_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_a_1018_);
lean_dec(v_a_1015_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_termMeasures_1005_);
lean_dec_ref(v_fixedArgs_1004_);
lean_dec_ref(v_argsPacker_1001_);
lean_dec_ref(v_argType_1000_);
v_a_1066_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1019_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1019_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_a_1015_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_termMeasures_1005_);
lean_dec_ref(v_fixedArgs_1004_);
lean_dec_ref(v_argsPacker_1001_);
lean_dec_ref(v_argType_1000_);
v_a_1074_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1017_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1017_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_termMeasures_1005_);
lean_dec_ref(v_fixedArgs_1004_);
lean_dec_ref(v_argsPacker_1001_);
lean_dec_ref(v_argType_1000_);
v_a_1082_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1014_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1014_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object* v_argType_1090_, lean_object* v_argsPacker_1091_, lean_object* v_declNames_1092_, lean_object* v_fixedParamPerms_1093_, lean_object* v_fixedArgs_1094_, lean_object* v_termMeasures_1095_, lean_object* v_k_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(v_argType_1090_, v_argsPacker_1091_, v_declNames_1092_, v_fixedParamPerms_1093_, v_fixedArgs_1094_, v_termMeasures_1095_, v_k_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_fixedParamPerms_1093_);
lean_dec_ref(v_declNames_1092_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object* v_declNames_1105_, lean_object* v_unaryPreDefName_1106_, lean_object* v_fixedParamPerms_1107_, lean_object* v_fixedArgs_1108_, lean_object* v_argsPacker_1109_, lean_object* v_argType_1110_, lean_object* v_termMeasures_1111_, lean_object* v_k_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1120_, 0, v_argType_1110_);
lean_closure_set(v___f_1120_, 1, v_argsPacker_1109_);
lean_closure_set(v___f_1120_, 2, v_declNames_1105_);
lean_closure_set(v___f_1120_, 3, v_fixedParamPerms_1107_);
lean_closure_set(v___f_1120_, 4, v_fixedArgs_1108_);
lean_closure_set(v___f_1120_, 5, v_termMeasures_1111_);
lean_closure_set(v___f_1120_, 6, v_k_1112_);
v___x_1121_ = l_Lean_Elab_Term_withDeclName___redArg(v_unaryPreDefName_1106_, v___f_1120_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object* v_declNames_1122_, lean_object* v_unaryPreDefName_1123_, lean_object* v_fixedParamPerms_1124_, lean_object* v_fixedArgs_1125_, lean_object* v_argsPacker_1126_, lean_object* v_argType_1127_, lean_object* v_termMeasures_1128_, lean_object* v_k_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1122_, v_unaryPreDefName_1123_, v_fixedParamPerms_1124_, v_fixedArgs_1125_, v_argsPacker_1126_, v_argType_1127_, v_termMeasures_1128_, v_k_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* v_00_u03b1_1138_, lean_object* v_declNames_1139_, lean_object* v_unaryPreDefName_1140_, lean_object* v_fixedParamPerms_1141_, lean_object* v_fixedArgs_1142_, lean_object* v_argsPacker_1143_, lean_object* v_argType_1144_, lean_object* v_termMeasures_1145_, lean_object* v_k_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Elab_WF_elabWFRel___redArg(v_declNames_1139_, v_unaryPreDefName_1140_, v_fixedParamPerms_1141_, v_fixedArgs_1142_, v_argsPacker_1143_, v_argType_1144_, v_termMeasures_1145_, v_k_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_declNames_1156_, lean_object* v_unaryPreDefName_1157_, lean_object* v_fixedParamPerms_1158_, lean_object* v_fixedArgs_1159_, lean_object* v_argsPacker_1160_, lean_object* v_argType_1161_, lean_object* v_termMeasures_1162_, lean_object* v_k_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Elab_WF_elabWFRel(v_00_u03b1_1155_, v_declNames_1156_, v_unaryPreDefName_1157_, v_fixedParamPerms_1158_, v_fixedArgs_1159_, v_argsPacker_1160_, v_argType_1161_, v_termMeasures_1162_, v_k_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object* v_fixedParamPerms_1172_, lean_object* v_fixedArgs_1173_, lean_object* v_as_1174_, size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_1172_, v_fixedArgs_1173_, v_sz_1175_, v_i_1176_, v_bs_1177_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object* v_fixedParamPerms_1186_, lean_object* v_fixedArgs_1187_, lean_object* v_as_1188_, lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
size_t v_sz_boxed_1199_; size_t v_i_boxed_1200_; lean_object* v_res_1201_; 
v_sz_boxed_1199_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1200_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_elabWFRel_spec__0(v_fixedParamPerms_1186_, v_fixedArgs_1187_, v_as_1188_, v_sz_boxed_1199_, v_i_boxed_1200_, v_bs_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_as_1188_);
lean_dec_ref(v_fixedParamPerms_1186_);
return v_res_1201_;
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
