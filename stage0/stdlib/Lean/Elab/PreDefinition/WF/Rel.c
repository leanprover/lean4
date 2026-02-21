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
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Elab.PreDefinition.WF.Rel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Elab.WF.checkCodomains"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: xs.size = arity\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "The termination measure's type must not depend on the "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_checkCodomains___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_checkCodomains___closed__0;
static const lean_ctor_object l_Lean_Elab_WF_checkCodomains___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_checkCodomains___closed__1 = (const lean_object*)&l_Lean_Elab_WF_checkCodomains___closed__1_value;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invImage"};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 194, 127, 152, 147, 1, 182, 44)}};
static const lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_obj_once(&l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0, &l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), x_1, x_2, x_13, x_4, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
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
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_instBEqFVarId_beq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(lean_object* x_1, lean_object* x_2) {
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
x_18 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_1, x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_1, x_16);
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
x_23 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_1, x_21);
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
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(x_1, x_27);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
block_8:
{
uint8_t x_6; 
x_6 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_1, x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(x_19, x_2);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(x_29, x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(x_11, x_12, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_7, 13);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set(x_31, 7, x_21);
lean_ctor_set(x_31, 8, x_22);
lean_ctor_set(x_31, 9, x_23);
lean_ctor_set(x_31, 10, x_24);
lean_ctor_set(x_31, 11, x_25);
lean_ctor_set(x_31, 12, x_27);
lean_ctor_set(x_31, 13, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_28);
x_32 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_8);
lean_dec_ref(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(33u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_eq(x_14, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
x_17 = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(x_16, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_array_size(x_5);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(x_18, x_19, x_5);
x_21 = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(x_20, x_6);
lean_dec_ref(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
x_24 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
x_25 = l_Lean_MessageData_ofName(x_2);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(x_4, x_35, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_6);
return x_36;
}
else
{
lean_object* x_39; 
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_6);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_6);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_24 = x_17;
} else {
 lean_dec_ref(x_17);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
x_27 = lean_ctor_get(x_18, 2);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_22;
}
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_18, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_18, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
x_39 = lean_ctor_get(x_21, 2);
x_40 = lean_array_fget(x_25, x_26);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_26, x_41);
lean_dec(x_26);
lean_ctor_set(x_18, 1, x_42);
x_43 = lean_nat_dec_lt(x_38, x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
if (lean_is_scalar(x_24)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_24;
}
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_22;
}
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_20)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_20;
}
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_inc(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_21, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_21, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_21, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_19, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_19, 1);
x_54 = lean_array_fget(x_37, x_38);
x_55 = lean_nat_add(x_38, x_41);
lean_dec(x_38);
lean_ctor_set(x_21, 1, x_55);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_60;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_nat_dec_lt(x_62, x_53);
if (x_63 == 0)
{
lean_free_object(x_52);
lean_dec(x_62);
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_60;
}
else
{
uint8_t x_64; 
lean_inc(x_53);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_19, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_19, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_40, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_68);
lean_dec(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_69 = lean_infer_type(x_68, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_73 = lean_array_get_borrowed(x_72, x_71, x_62);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_73);
x_74 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_73, x_70, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_75);
lean_inc(x_76);
lean_inc(x_54);
x_77 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(x_77, 0, x_54);
lean_closure_set(x_77, 1, x_76);
lean_closure_set(x_77, 2, x_75);
lean_closure_set(x_77, 3, x_67);
lean_ctor_set(x_52, 0, x_54);
x_78 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_79 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_75, x_52, x_77, x_78, x_78, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_nat_add(x_62, x_41);
lean_dec(x_62);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_19, 0, x_82);
x_83 = lean_array_push(x_23, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_18);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_21);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_19);
lean_ctor_set(x_86, 1, x_85);
x_87 = 1;
x_88 = lean_usize_add(x_5, x_87);
x_5 = x_88;
x_6 = x_86;
goto _start;
}
else
{
uint8_t x_90; 
lean_free_object(x_19);
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
return x_79;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
lean_dec(x_79);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_67);
lean_free_object(x_19);
lean_free_object(x_52);
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_93 = !lean_is_exclusive(x_74);
if (x_93 == 0)
{
return x_74;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_74, 0);
lean_inc(x_94);
lean_dec(x_74);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_67);
lean_free_object(x_19);
lean_free_object(x_52);
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_96 = !lean_is_exclusive(x_69);
if (x_96 == 0)
{
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_69, 0);
lean_inc(x_97);
lean_dec(x_69);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_19);
x_99 = lean_ctor_get(x_40, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_100);
lean_dec(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_101 = lean_infer_type(x_100, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_ctor_get(x_1, 1);
x_104 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_105 = lean_array_get_borrowed(x_104, x_103, x_62);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_105);
x_106 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_105, x_102, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_107);
lean_inc(x_108);
lean_inc(x_54);
x_109 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(x_109, 0, x_54);
lean_closure_set(x_109, 1, x_108);
lean_closure_set(x_109, 2, x_107);
lean_closure_set(x_109, 3, x_99);
lean_ctor_set(x_52, 0, x_54);
x_110 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_111 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_107, x_52, x_109, x_110, x_110, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; size_t x_120; size_t x_121; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_nat_add(x_62, x_41);
lean_dec(x_62);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_53);
x_116 = lean_array_push(x_23, x_112);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_21);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = 1;
x_121 = lean_usize_add(x_5, x_120);
x_5 = x_121;
x_6 = x_119;
goto _start;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_123 = lean_ctor_get(x_111, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_99);
lean_free_object(x_52);
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_126 = lean_ctor_get(x_106, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_127 = x_106;
} else {
 lean_dec_ref(x_106);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_99);
lean_free_object(x_52);
lean_dec(x_62);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_129 = lean_ctor_get(x_101, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_130 = x_101;
} else {
 lean_dec_ref(x_101);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
return x_131;
}
}
}
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_52, 0);
lean_inc(x_132);
lean_dec(x_52);
x_133 = lean_nat_dec_lt(x_132, x_53);
if (x_133 == 0)
{
lean_dec(x_132);
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_60;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_53);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_134 = x_19;
} else {
 lean_dec_ref(x_19);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_40, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_136);
lean_dec(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_137 = lean_infer_type(x_136, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_ctor_get(x_1, 1);
x_140 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_141 = lean_array_get_borrowed(x_140, x_139, x_132);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_141);
x_142 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_141, x_138, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_143);
lean_inc(x_144);
lean_inc(x_54);
x_145 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(x_145, 0, x_54);
lean_closure_set(x_145, 1, x_144);
lean_closure_set(x_145, 2, x_143);
lean_closure_set(x_145, 3, x_135);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_54);
x_147 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_148 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_143, x_146, x_145, x_147, x_147, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_nat_add(x_132, x_41);
lean_dec(x_132);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
if (lean_is_scalar(x_134)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_134;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_53);
x_153 = lean_array_push(x_23, x_149);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_18);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_21);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = 1;
x_158 = lean_usize_add(x_5, x_157);
x_5 = x_158;
x_6 = x_156;
goto _start;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec_ref(x_21);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_160 = lean_ctor_get(x_148, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_161 = x_148;
} else {
 lean_dec_ref(x_148);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_163 = lean_ctor_get(x_142, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_164 = x_142;
} else {
 lean_dec_ref(x_142);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec_ref(x_21);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_166 = lean_ctor_get(x_137, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_167 = x_137;
} else {
 lean_dec_ref(x_137);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
}
}
block_60:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_scalar(x_24)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_24;
}
lean_ctor_set(x_56, 0, x_18);
lean_ctor_set(x_56, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_22;
}
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_20)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_20;
}
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_21);
x_169 = lean_ctor_get(x_19, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_19, 1);
x_171 = lean_array_fget(x_37, x_38);
x_172 = lean_nat_add(x_38, x_41);
lean_dec(x_38);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_37);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_39);
if (lean_obj_tag(x_169) == 0)
{
lean_dec(x_171);
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_178;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_180 = x_169;
} else {
 lean_dec_ref(x_169);
 x_180 = lean_box(0);
}
x_181 = lean_nat_dec_lt(x_179, x_170);
if (x_181 == 0)
{
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_171);
lean_dec(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_178;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_inc(x_170);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_182 = x_19;
} else {
 lean_dec_ref(x_19);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_40, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_184);
lean_dec(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_185 = lean_infer_type(x_184, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = lean_ctor_get(x_1, 1);
x_188 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_189 = lean_array_get_borrowed(x_188, x_187, x_179);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_189);
x_190 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_189, x_186, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_191);
lean_inc(x_192);
lean_inc(x_171);
x_193 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(x_193, 0, x_171);
lean_closure_set(x_193, 1, x_192);
lean_closure_set(x_193, 2, x_191);
lean_closure_set(x_193, 3, x_183);
if (lean_is_scalar(x_180)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_180;
}
lean_ctor_set(x_194, 0, x_171);
x_195 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_196 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_191, x_194, x_193, x_195, x_195, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; size_t x_206; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = lean_nat_add(x_179, x_41);
lean_dec(x_179);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_182)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_182;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_170);
x_201 = lean_array_push(x_23, x_197);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_18);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_173);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_200);
lean_ctor_set(x_204, 1, x_203);
x_205 = 1;
x_206 = lean_usize_add(x_5, x_205);
x_5 = x_206;
x_6 = x_204;
goto _start;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_182);
lean_dec(x_179);
lean_dec_ref(x_173);
lean_dec(x_170);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_208 = lean_ctor_get(x_196, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_209 = x_196;
} else {
 lean_dec_ref(x_196);
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
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_211 = lean_ctor_get(x_190, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_212 = x_190;
} else {
 lean_dec_ref(x_190);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec_ref(x_18);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_214 = lean_ctor_get(x_185, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_215 = x_185;
} else {
 lean_dec_ref(x_185);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
}
block_178:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
if (lean_is_scalar(x_24)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_24;
}
lean_ctor_set(x_174, 0, x_18);
lean_ctor_set(x_174, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_22;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_20)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_20;
}
lean_ctor_set(x_176, 0, x_19);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_18);
x_217 = lean_ctor_get(x_21, 0);
x_218 = lean_ctor_get(x_21, 1);
x_219 = lean_ctor_get(x_21, 2);
x_220 = lean_array_fget(x_25, x_26);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_26, x_221);
lean_dec(x_26);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_25);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_27);
x_224 = lean_nat_dec_lt(x_218, x_219);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_220);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
if (lean_is_scalar(x_24)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_24;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_22;
}
lean_ctor_set(x_226, 0, x_21);
lean_ctor_set(x_226, 1, x_225);
if (lean_is_scalar(x_20)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_20;
}
lean_ctor_set(x_227, 0, x_19);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_inc(x_219);
lean_inc(x_218);
lean_inc_ref(x_217);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_229 = x_21;
} else {
 lean_dec_ref(x_21);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_19, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_19, 1);
x_232 = lean_array_fget(x_217, x_218);
x_233 = lean_nat_add(x_218, x_221);
lean_dec(x_218);
if (lean_is_scalar(x_229)) {
 x_234 = lean_alloc_ctor(0, 3, 0);
} else {
 x_234 = x_229;
}
lean_ctor_set(x_234, 0, x_217);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_219);
if (lean_obj_tag(x_230) == 0)
{
lean_dec(x_232);
lean_dec(x_220);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_239;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = lean_ctor_get(x_230, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_241 = x_230;
} else {
 lean_dec_ref(x_230);
 x_241 = lean_box(0);
}
x_242 = lean_nat_dec_lt(x_240, x_231);
if (x_242 == 0)
{
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_232);
lean_dec(x_220);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
goto block_239;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_inc(x_231);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_243 = x_19;
} else {
 lean_dec_ref(x_19);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_220, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_220, 1);
lean_inc_ref(x_245);
lean_dec(x_220);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_246 = lean_infer_type(x_245, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = lean_ctor_get(x_1, 1);
x_249 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_250 = lean_array_get_borrowed(x_249, x_248, x_240);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_250);
x_251 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_250, x_247, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_252);
lean_inc(x_253);
lean_inc(x_232);
x_254 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed), 13, 4);
lean_closure_set(x_254, 0, x_232);
lean_closure_set(x_254, 1, x_253);
lean_closure_set(x_254, 2, x_252);
lean_closure_set(x_254, 3, x_244);
if (lean_is_scalar(x_241)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_241;
}
lean_ctor_set(x_255, 0, x_232);
x_256 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_257 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(x_252, x_255, x_254, x_256, x_256, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; size_t x_266; size_t x_267; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = lean_nat_add(x_240, x_221);
lean_dec(x_240);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_243)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_243;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_231);
x_262 = lean_array_push(x_23, x_258);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_223);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_234);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_264);
x_266 = 1;
x_267 = lean_usize_add(x_5, x_266);
x_5 = x_267;
x_6 = x_265;
goto _start;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_243);
lean_dec(x_240);
lean_dec_ref(x_234);
lean_dec(x_231);
lean_dec_ref(x_223);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_269 = lean_ctor_get(x_257, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_270 = x_257;
} else {
 lean_dec_ref(x_257);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_234);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_223);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_272 = lean_ctor_get(x_251, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_273 = x_251;
} else {
 lean_dec_ref(x_251);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_234);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_223);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_275 = lean_ctor_get(x_246, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_276 = x_246;
} else {
 lean_dec_ref(x_246);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
}
block_239:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
if (lean_is_scalar(x_24)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_24;
}
lean_ctor_set(x_235, 0, x_223);
lean_ctor_set(x_235, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_22;
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
if (lean_is_scalar(x_20)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_20;
}
lean_ctor_set(x_237, 0, x_19);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_6, x_1);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget_borrowed(x_2, x_6);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_23);
lean_inc_ref(x_3);
x_24 = l_Lean_Meta_isExprDefEqGuarded(x_3, x_23, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_box(0);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_28 = l_Lean_Elab_instInhabitedTerminationMeasure_default;
x_29 = lean_array_get_borrowed(x_28, x_4, x_6);
x_30 = lean_ctor_get(x_29, 0);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
x_33 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
x_34 = lean_box(0);
x_35 = lean_array_get_borrowed(x_34, x_5, x_31);
lean_inc(x_35);
x_36 = l_Lean_MessageData_ofName(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
lean_inc_ref(x_3);
x_41 = l_Lean_indentExpr(x_3);
x_42 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
x_46 = lean_array_get_borrowed(x_34, x_5, x_6);
lean_inc(x_46);
x_47 = l_Lean_MessageData_ofName(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
lean_inc(x_23);
x_50 = l_Lean_indentExpr(x_23);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_12);
lean_inc_ref(x_8);
x_56 = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(x_30, x_55, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_15 = x_26;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_56;
}
}
else
{
x_15 = x_26;
x_16 = lean_box(0);
goto block_20;
}
}
else
{
uint8_t x_57; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_24, 0);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_6 = x_18;
x_7 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_WF_checkCodomains___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_obj_once(&l_Lean_Elab_WF_checkCodomains___closed__0, &l_Lean_Elab_WF_checkCodomains___closed__0_once, _init_l_Lean_Elab_WF_checkCodomains___closed__0);
x_15 = lean_array_get_size(x_1);
x_16 = ((lean_object*)(l_Lean_Elab_WF_checkCodomains___closed__1));
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_get_size(x_4);
x_19 = l_Array_toSubarray___redArg(x_4, x_13, x_18);
x_20 = lean_array_get_size(x_5);
lean_inc_ref(x_5);
x_21 = l_Array_toSubarray___redArg(x_5, x_13, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_size(x_1);
x_26 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(x_2, x_3, x_1, x_25, x_26, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_get_size(x_31);
x_35 = lean_array_get(x_32, x_31, x_13);
x_36 = lean_box(0);
lean_inc(x_35);
x_37 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(x_34, x_31, x_35, x_5, x_1, x_33, x_36, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_31);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_35);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_WF_checkCodomains(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(lean_object** _args) {
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
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
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
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(x_1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_4, x_12);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_array_fget_borrowed(x_3, x_5);
x_17 = lean_ctor_get(x_16, 1);
x_18 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
x_19 = lean_array_get_borrowed(x_18, x_15, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_17);
lean_inc(x_19);
x_20 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_19, x_17, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_4, x_22);
lean_dec(x_4);
x_24 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_25 = lean_array_push(x_6, x_21);
x_4 = x_23;
x_5 = x_24;
x_6 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_getLevel(x_1, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_ArgsPacker_arities(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_18 = l_Lean_Elab_WF_checkCodomains(x_3, x_4, x_5, x_17, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_19);
x_20 = l_Lean_Meta_getLevel(x_19, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_array_get_size(x_6);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_22);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_25 = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(x_4, x_5, x_6, x_22, x_23, x_24, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_27 = l_Lean_Meta_ArgsPacker_uncurryND(x_2, x_26, x_10, x_11, x_12, x_13);
lean_dec(x_26);
lean_dec_ref(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1));
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_const___override(x_29, x_31);
lean_inc(x_19);
x_33 = l_Lean_Expr_app___override(x_32, x_19);
x_34 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_35 = l_Lean_Meta_synthInstance(x_33, x_34, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3));
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_31);
x_39 = l_Lean_Expr_const___override(x_37, x_38);
x_40 = l_Lean_mkApp4(x_39, x_1, x_19, x_28, x_36);
x_41 = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(x_40, x_11);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_apply_8(x_7, x_42, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_43;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_31);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_27, 0);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
lean_dec(x_25);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_18);
if (x_56 == 0)
{
return x_18;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_18, 0);
lean_inc(x_57);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed), 14, 7);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_7);
lean_closure_set(x_16, 6, x_8);
x_17 = l_Lean_Elab_Term_withDeclName___redArg(x_2, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_WF_elabWFRel___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_WF_elabWFRel___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_WF_elabWFRel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
