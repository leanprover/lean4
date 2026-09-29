// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Postponed
// Imports: public import Lean.Elab.Term.TermElabM public import Lean.DocString.DeferredCheck
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_Doc_deferredCheckExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Core_Context_setOptions(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deferred"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 182, 57, 82, 86, 77, 242, 57)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(129, 127, 0, 79, 118, 118, 4, 216)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "if true, run the deferred checks recorded while elaborating Verso docstrings"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 182, 224, 198, 198, 122, 225, 30)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 165, 182, 144, 148, 234, 72, 121)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(8, 119, 36, 37, 165, 14, 86, 85)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_linter_doc_deferred;
static const lean_string_object l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PostponedName"};
static const lean_object* l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(167, 68, 121, 121, 24, 14, 202, 161)}};
static const lean_object* l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instTypeNamePostponedName = (const lean_object*)&l_Lean_Doc_instImpl___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PostponedKind"};
static const lean_object* l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(4, 126, 152, 146, 251, 151, 37, 250)}};
static const lean_object* l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instTypeNamePostponedKind = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DeferredCheck"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "handlerExt"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 254, 44, 225, 102, 40, 150, 242)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 216, 14, 79, 12, 54, 251, 118)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_handlerExt;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_builtinHandlers;
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "DeferredCheckHandler"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 146, 221, 208, 194, 218, 14, 77)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "invalid `deferred_doc_check` syntax"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `deferred_doc_check`, must be global"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 232, 180, 69, 21, 196, 130, 34)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Builtin"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 234, 185, 91, 95, 3, 186, 9)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Postponed"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 157, 46, 149, 46, 140, 10, 151)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__11_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(233, 19, 92, 122, 138, 229, 76, 241)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__11_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__11_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__12_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__11_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(172, 125, 105, 245, 60, 156, 60, 228)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__12_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__12_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__13_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__12_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(44, 223, 147, 219, 181, 243, 244, 167)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__13_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__13_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__14_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__13_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 148, 17, 166, 228, 248, 241, 59)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__14_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__14_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__15_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__15_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__15_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__16_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__14_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__15_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 87, 53, 45, 112, 84, 211, 6)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__16_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__16_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__17_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__17_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__17_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__18_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__16_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__17_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 141, 104, 180, 34, 241, 16, 184)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__18_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__18_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__19_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__18_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(129, 57, 204, 31, 6, 250, 95, 238)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__19_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__19_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__20_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__19_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 42, 97, 104, 169, 21, 183, 237)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__20_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__20_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__21_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__20_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 23, 161, 205, 13, 99, 57, 155)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__21_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__21_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__22_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__21_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(164, 7, 149, 39, 46, 219, 200, 57)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__22_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__22_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__23_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__22_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 237, 57, 148, 43, 46, 48, 73)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__23_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__23_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__24_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__23_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1993970768) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 212, 205, 231, 97, 245, 140, 120)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__24_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__24_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__25_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__25_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__25_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__26_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__24_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__25_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 110, 54, 250, 48, 243, 179, 226)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__26_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__26_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__27_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__27_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__27_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__28_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__26_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__27_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 175, 136, 19, 110, 2, 42, 22)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__28_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__28_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__29_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__28_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(6, 153, 195, 37, 142, 116, 52, 138)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__29_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__29_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__30_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "deferred_doc_check"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__30_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__30_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__30_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 224, 174, 180, 143, 211, 85, 153)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__33_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__33_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__33_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__34_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "Registers a `DeferredCheckHandler` for deferred docstring checks whose data has the named type."};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__34_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__34_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__35_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__29_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__34_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__35_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__35_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__35_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__33_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "addBuiltinHandler"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "invalid `builtin_deferred_doc_check` syntax"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "invalid attribute `builtin_deferred_doc_check`, must be global"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__23_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),((lean_object*)(((size_t)(195487833) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(153, 186, 18, 229, 168, 251, 64, 116)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__25_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 105, 38, 48, 177, 8, 240, 77)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__27_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 49, 208, 203, 68, 192, 45, 219)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(119, 183, 244, 233, 170, 194, 168, 64)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "builtin_deferred_doc_check"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 167, 152, 24, 233, 41, 21, 93)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Registers a builtin `DeferredCheckHandler` for deferred docstring checks whose data has the named type."};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "no handler registered for deferred check `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "the check requires "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " to be imported, but they are not"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_DeferredCheck_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_DeferredCheck_run___closed__0 = (const lean_object*)&l_Lean_Doc_DeferredCheck_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_m_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___x_79_; 
v_fst_77_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_fst_77_);
v_snd_78_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_snd_78_);
lean_dec_ref(v_x_76_);
v___x_79_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_77_, v_snd_78_, v_m_75_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_88_; size_t v___x_89_; size_t v___x_90_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
v_fst_86_ = lean_ctor_get(v___x_85_, 0);
v_snd_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_snd_87_);
lean_inc(v_fst_86_);
v___x_88_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_86_, v_snd_87_, v_b_83_);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_81_, v___x_89_);
v_i_81_ = v___x_90_;
v_b_83_ = v___x_88_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_92_, lean_object* v_i_93_, lean_object* v_stop_94_, lean_object* v_b_95_){
_start:
{
size_t v_i_boxed_96_; size_t v_stop_boxed_97_; lean_object* v_res_98_; 
v_i_boxed_96_ = lean_unbox_usize(v_i_93_);
lean_dec(v_i_93_);
v_stop_boxed_97_ = lean_unbox_usize(v_stop_94_);
lean_dec(v_stop_94_);
v_res_98_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(v_as_92_, v_i_boxed_96_, v_stop_boxed_97_, v_b_95_);
lean_dec_ref(v_as_92_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(lean_object* v_as_99_, size_t v_i_100_, size_t v_stop_101_, lean_object* v_b_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_100_, v_stop_101_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v_fst_105_; lean_object* v_snd_106_; lean_object* v___x_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_104_ = lean_array_uget_borrowed(v_as_99_, v_i_100_);
v_fst_105_ = lean_ctor_get(v___x_104_, 0);
v_snd_106_ = lean_ctor_get(v___x_104_, 1);
lean_inc(v_snd_106_);
lean_inc(v_fst_105_);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_105_, v_snd_106_, v_b_102_);
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_add(v_i_100_, v___x_108_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(v_as_99_, v___x_109_, v_stop_101_, v___x_107_);
return v___x_110_;
}
else
{
return v_b_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_, lean_object* v_b_114_){
_start:
{
size_t v_i_boxed_115_; size_t v_stop_boxed_116_; lean_object* v_res_117_; 
v_i_boxed_115_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_116_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v_as_111_, v_i_boxed_115_, v_stop_boxed_116_, v_b_114_);
lean_dec_ref(v_as_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(lean_object* v_as_118_, size_t v_i_119_, size_t v_stop_120_, lean_object* v_b_121_){
_start:
{
lean_object* v___y_123_; uint8_t v___x_127_; 
v___x_127_ = lean_usize_dec_eq(v_i_119_, v_stop_120_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_array_uget_borrowed(v_as_118_, v_i_119_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_array_get_size(v___x_128_);
v___x_131_ = lean_nat_dec_lt(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
v___y_123_ = v_b_121_;
goto v___jp_122_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_le(v___x_130_, v___x_130_);
if (v___x_132_ == 0)
{
if (v___x_131_ == 0)
{
v___y_123_ = v_b_121_;
goto v___jp_122_;
}
else
{
size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((size_t)0ULL);
v___x_134_ = lean_usize_of_nat(v___x_130_);
v___x_135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v___x_128_, v___x_133_, v___x_134_, v_b_121_);
v___y_123_ = v___x_135_;
goto v___jp_122_;
}
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_130_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v___x_128_, v___x_136_, v___x_137_, v_b_121_);
v___y_123_ = v___x_138_;
goto v___jp_122_;
}
}
}
else
{
return v_b_121_;
}
v___jp_122_:
{
size_t v___x_124_; size_t v___x_125_; 
v___x_124_ = ((size_t)1ULL);
v___x_125_ = lean_usize_add(v_i_119_, v___x_124_);
v_i_119_ = v___x_125_;
v_b_121_ = v___y_123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_139_, lean_object* v_i_140_, lean_object* v_stop_141_, lean_object* v_b_142_){
_start:
{
size_t v_i_boxed_143_; size_t v_stop_boxed_144_; lean_object* v_res_145_; 
v_i_boxed_143_ = lean_unbox_usize(v_i_140_);
lean_dec(v_i_140_);
v_stop_boxed_144_ = lean_unbox_usize(v_stop_141_);
lean_dec(v_stop_141_);
v_res_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_as_139_, v_i_boxed_143_, v_stop_boxed_144_, v_b_142_);
lean_dec_ref(v_as_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_nss_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_147_ = lean_box(1);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_array_get_size(v_nss_146_);
v___x_150_ = lean_nat_dec_lt(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
return v___x_147_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v___x_149_, v___x_149_);
if (v___x_151_ == 0)
{
if (v___x_150_ == 0)
{
return v___x_147_;
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_149_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_nss_146_, v___x_152_, v___x_153_, v___x_147_);
return v___x_154_;
}
}
else
{
size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((size_t)0ULL);
v___x_156_ = lean_usize_of_nat(v___x_149_);
v___x_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_nss_146_, v___x_155_, v___x_156_, v___x_147_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_nss_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(v_nss_158_);
lean_dec_ref(v_nss_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_es_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_array_mk(v_es_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_));
v___x_181_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_box(1);
v___x_186_ = lean_st_mk_ref(v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2____boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler(lean_object* v_key_190_, lean_object* v_impl_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_194_ = lean_st_ref_take(v___x_193_);
v___x_195_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_key_190_, v_impl_191_, v___x_194_);
v___x_196_ = lean_st_ref_put(v___x_193_, v___x_195_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler___boxed(lean_object* v_key_198_, lean_object* v_impl_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Doc_DeferredCheck_addBuiltinHandler(v_key_198_, v_impl_199_);
return v_res_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
lean_ctor_set(v___x_207_, 3, v___x_206_);
lean_ctor_set(v___x_207_, 4, v___x_205_);
lean_ctor_set(v___x_207_, 5, v___x_205_);
lean_ctor_set(v___x_207_, 6, v___x_205_);
lean_ctor_set(v___x_207_, 7, v___x_205_);
lean_ctor_set(v___x_207_, 8, v___x_205_);
lean_ctor_set(v___x_207_, 9, v___x_205_);
lean_ctor_set(v___x_207_, 10, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(32u);
v___x_209_ = lean_mk_empty_array_with_capacity(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_211_ = ((size_t)5ULL);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_unsigned_to_nat(32u);
v___x_214_ = lean_mk_empty_array_with_capacity(v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_216_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_212_);
lean_ctor_set(v___x_216_, 3, v___x_212_);
lean_ctor_set_usize(v___x_216_, 4, v___x_211_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_box(1);
v___x_218_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v_toCold_226_; lean_object* v_env_227_; lean_object* v_options_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_225_ = lean_st_ref_get(v___y_223_);
v_toCold_226_ = lean_ctor_get(v___y_222_, 0);
v_env_227_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_227_);
lean_dec(v___x_225_);
v_options_228_ = lean_ctor_get(v_toCold_226_, 2);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_228_);
v___x_231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_231_, 0, v_env_227_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_ctor_set(v___x_231_, 3, v_options_228_);
v___x_232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_msgData_221_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_ref_243_; lean_object* v___x_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
v_ref_243_ = lean_ctor_get(v___y_240_, 2);
v___x_244_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_239_, v___y_240_, v___y_241_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_ref_243_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_ref_243_);
lean_ctor_set(v___x_249_, 1, v_a_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 1);
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_x_259_, 1);
v___x_264_ = l_Lean_stringToMessageData(v_a_263_);
v___x_265_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_264_, v___y_260_, v___y_261_);
return v___x_265_;
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v_x_259_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v_x_259_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v_x_259_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_box(0);
v___x_280_ = l_Lean_Elab_abortCommandExceptionId;
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(lean_object* v_typeName_287_, lean_object* v_constName_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; lean_object* v_env_293_; uint8_t v___x_294_; 
v___x_292_ = lean_st_ref_get(v___y_290_);
v_env_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_env_293_);
lean_dec(v___x_292_);
lean_inc(v_constName_288_);
v___x_294_ = lean_has_compile_error(v_env_293_, v_constName_288_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v_env_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_295_ = lean_st_ref_get(v___y_290_);
v_env_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_ref(v_env_296_);
lean_dec(v___x_295_);
v___x_297_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_289_);
v___x_298_ = l_Lean_Environment_evalConstCheck___redArg(v_env_296_, v___x_297_, v_typeName_287_, v_constName_288_);
lean_dec_ref(v___x_297_);
v___x_299_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_298_, v___y_289_, v___y_290_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref_known(v___x_300_, 1);
v___x_301_ = lean_st_ref_get(v___y_290_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v___x_303_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_289_);
v___x_304_ = l_Lean_Environment_evalConstCheck___redArg(v_env_302_, v___x_303_, v_typeName_287_, v_constName_288_);
lean_dec_ref(v___x_303_);
v___x_305_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_304_, v___y_289_, v___y_290_);
return v___x_305_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_constName_288_);
lean_dec(v_typeName_287_);
v_a_306_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_300_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_300_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_314_, lean_object* v_constName_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_314_, v_constName_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(lean_object* v_declName_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1));
v___x_330_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v___x_329_, v_declName_325_, v_a_326_, v_a_327_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___boxed(lean_object* v_declName_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_declName_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_object* v_00_u03b1_346_, lean_object* v_typeName_347_, lean_object* v_constName_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_347_, v_constName_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_353_, lean_object* v_typeName_354_, lean_object* v_constName_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(v_00_u03b1_353_, v_typeName_354_, v_constName_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_360_, lean_object* v_x_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_361_, v___y_362_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_366_, v_x_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_378_, v_msg_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_decl_401_, lean_object* v_stx_402_, uint8_t v_kind_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_key_408_; lean_object* v___y_409_; uint8_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 0;
v___x_490_ = l_Lean_instBEqAttributeKind_beq(v_kind_403_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec_ref(v___x_398_);
lean_dec(v___x_397_);
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_492_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_491_, v___y_404_, v___y_405_);
return v___x_492_;
}
else
{
goto v___jp_437_;
}
v___jp_407_:
{
lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_traceState_415_; lean_object* v_recordedDeps_416_; lean_object* v_messages_417_; lean_object* v_infoState_418_; lean_object* v_snapshotTasks_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_435_; 
v___x_410_ = lean_st_ref_take(v___y_409_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_410_, 1);
v_ngen_413_ = lean_ctor_get(v___x_410_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_410_, 3);
v_traceState_415_ = lean_ctor_get(v___x_410_, 4);
v_recordedDeps_416_ = lean_ctor_get(v___x_410_, 6);
v_messages_417_ = lean_ctor_get(v___x_410_, 7);
v_infoState_418_ = lean_ctor_get(v___x_410_, 8);
v_snapshotTasks_419_ = lean_ctor_get(v___x_410_, 9);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v___x_410_, 5);
lean_dec(v_unused_436_);
v___x_421_ = v___x_410_;
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snapshotTasks_419_);
lean_inc(v_infoState_418_);
lean_inc(v_messages_417_);
lean_inc(v_recordedDeps_416_);
lean_inc(v_traceState_415_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_410_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v_toEnvExtension_424_; lean_object* v_asyncMode_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_423_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_424_ = lean_ctor_get(v___x_423_, 0);
v_asyncMode_425_ = lean_ctor_get(v_toEnvExtension_424_, 2);
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_key_408_);
lean_ctor_set(v___x_427_, 1, v_decl_401_);
v___x_428_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_423_, v_env_411_, v___x_427_, v_asyncMode_425_, v___x_397_);
v___x_429_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 5, v___x_429_);
lean_ctor_set(v___x_421_, 0, v___x_428_);
v___x_431_ = v___x_421_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_traceState_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v_recordedDeps_416_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_messages_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 8, v_infoState_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 9, v_snapshotTasks_419_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_st_ref_put(v___y_409_, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_426_);
return v___x_433_;
}
}
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_439_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_440_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_441_ = l_Lean_Name_mkStr4(v___x_398_, v___x_438_, v___x_439_, v___x_440_);
lean_inc(v_stx_402_);
v___x_442_ = l_Lean_Syntax_isOfKind(v_stx_402_, v___x_441_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_443_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_444_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_443_, v___y_404_, v___y_405_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
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
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = l_Lean_Syntax_getArg(v_stx_402_, v___x_399_);
v___x_454_ = l_Lean_Syntax_matchesIdent(v___x_453_, v___x_400_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_455_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_456_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_455_, v___y_404_, v___y_405_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = l_Lean_Syntax_getArg(v_stx_402_, v___x_465_);
lean_dec(v_stx_402_);
lean_inc(v___x_466_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_466_, v___x_465_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec(v___x_466_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_468_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_469_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_468_, v___y_404_, v___y_405_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = l_Lean_Syntax_getArg(v___x_466_, v___x_399_);
lean_dec(v___x_466_);
v___x_479_ = l_Lean_realizeGlobalConstNoOverload(v___x_478_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_key_408_ = v_a_480_;
v___y_409_ = v___y_405_;
goto v___jp_407_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v_a_481_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_decl_497_, lean_object* v_stx_498_, lean_object* v_kind_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v_kind_boxed_503_; lean_object* v_res_504_; 
v_kind_boxed_503_ = lean_unbox(v_kind_499_);
v_res_504_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_493_, v___x_494_, v___x_495_, v___x_496_, v_decl_497_, v_stx_498_, v_kind_boxed_503_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___x_496_);
lean_dec(v___x_495_);
return v_res_504_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_510_ = l_Lean_stringToMessageData(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_511_, lean_object* v_decl_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_516_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_517_ = l_Lean_MessageData_ofName(v___x_511_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_520_, v___y_513_, v___y_514_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_522_, lean_object* v_decl_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_522_, v_decl_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v_decl_523_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_622_ = l_Lean_registerBuiltinAttribute(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
return v_res_624_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v_decl_637_, lean_object* v_stx_638_, uint8_t v_kind_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_key_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 0;
v___x_708_ = l_Lean_instBEqAttributeKind_beq(v_kind_639_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_stx_638_);
lean_dec(v_decl_637_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
v___x_709_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_710_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_709_, v___y_640_, v___y_641_);
return v___x_710_;
}
else
{
goto v___jp_655_;
}
v___jp_643_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_648_ = l_Lean_Name_mkStr4(v___x_632_, v___x_633_, v___x_634_, v___x_647_);
v___x_649_ = lean_box(0);
v___x_650_ = l_Lean_Expr_const___override(v___x_648_, v___x_649_);
v___x_651_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_key_644_);
lean_inc(v_decl_637_);
v___x_652_ = l_Lean_Expr_const___override(v_decl_637_, v___x_649_);
v___x_653_ = l_Lean_mkAppB(v___x_650_, v___x_651_, v___x_652_);
v___x_654_ = l_Lean_declareBuiltin(v_decl_637_, v___x_653_, v___y_645_, v___y_646_);
return v___x_654_;
}
v___jp_655_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
lean_inc_ref(v___x_632_);
v___x_659_ = l_Lean_Name_mkStr4(v___x_632_, v___x_656_, v___x_657_, v___x_658_);
lean_inc(v_stx_638_);
v___x_660_ = l_Lean_Syntax_isOfKind(v_stx_638_, v___x_659_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_stx_638_);
lean_dec(v_decl_637_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
v___x_661_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_662_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_661_, v___y_640_, v___y_641_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_635_);
v___x_672_ = l_Lean_Syntax_matchesIdent(v___x_671_, v___x_636_);
lean_dec(v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_stx_638_);
lean_dec(v_decl_637_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
v___x_673_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_674_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_673_, v___y_640_, v___y_641_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_683_);
lean_dec(v_stx_638_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_Syntax_matchesNull(v___x_684_, v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v___x_684_);
lean_dec(v_decl_637_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
v___x_686_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_687_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_686_, v___y_640_, v___y_641_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Lean_Syntax_getArg(v___x_684_, v___x_635_);
lean_dec(v___x_684_);
v___x_697_ = l_Lean_realizeGlobalConstNoOverload(v___x_696_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v_key_644_ = v_a_698_;
v___y_645_ = v___y_640_;
v___y_646_ = v___y_641_;
goto v___jp_643_;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_decl_637_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
v_a_699_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v_decl_716_, lean_object* v_stx_717_, lean_object* v_kind_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v_kind_boxed_722_; lean_object* v_res_723_; 
v_kind_boxed_722_ = lean_unbox(v_kind_718_);
v_res_723_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(v___x_711_, v___x_712_, v___x_713_, v___x_714_, v___x_715_, v_decl_716_, v_stx_717_, v_kind_boxed_722_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___x_715_);
lean_dec(v___x_714_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_759_ = l_Lean_registerBuiltinAttribute(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(lean_object* v_c_762_, lean_object* v_act_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_currNamespace_767_; lean_object* v_openDecls_768_; lean_object* v_options_769_; lean_object* v___x_770_; lean_object* v_toCold_771_; lean_object* v_currRecDepth_772_; lean_object* v_ref_773_; uint16_t v_optionFlags_774_; uint8_t v_suppressElabErrors_775_; uint8_t v_isRecordingDeps_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_803_; 
v_currNamespace_767_ = lean_ctor_get(v_c_762_, 4);
lean_inc(v_currNamespace_767_);
v_openDecls_768_ = lean_ctor_get(v_c_762_, 5);
lean_inc(v_openDecls_768_);
v_options_769_ = lean_ctor_get(v_c_762_, 6);
lean_inc_ref(v_options_769_);
lean_dec_ref(v_c_762_);
lean_inc_ref(v_a_764_);
v___x_770_ = l_Lean_Core_Context_setOptions(v_a_764_, v_options_769_);
v_toCold_771_ = lean_ctor_get(v___x_770_, 0);
v_currRecDepth_772_ = lean_ctor_get(v___x_770_, 1);
v_ref_773_ = lean_ctor_get(v___x_770_, 2);
v_optionFlags_774_ = lean_ctor_get_uint16(v___x_770_, sizeof(void*)*3);
v_suppressElabErrors_775_ = lean_ctor_get_uint8(v___x_770_, sizeof(void*)*3 + 2);
v_isRecordingDeps_776_ = lean_ctor_get_uint8(v___x_770_, sizeof(void*)*3 + 3);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_803_ == 0)
{
v___x_778_ = v___x_770_;
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_ref_773_);
lean_inc(v_currRecDepth_772_);
lean_inc(v_toCold_771_);
lean_dec(v___x_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fileName_780_; lean_object* v_fileMap_781_; lean_object* v_options_782_; lean_object* v_maxRecDepth_783_; lean_object* v_initHeartbeats_784_; lean_object* v_maxHeartbeats_785_; lean_object* v_quotContext_786_; lean_object* v_currMacroScope_787_; lean_object* v_cancelTk_x3f_788_; lean_object* v_inheritedTraceOptions_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_800_; 
v_fileName_780_ = lean_ctor_get(v_toCold_771_, 0);
v_fileMap_781_ = lean_ctor_get(v_toCold_771_, 1);
v_options_782_ = lean_ctor_get(v_toCold_771_, 2);
v_maxRecDepth_783_ = lean_ctor_get(v_toCold_771_, 3);
v_initHeartbeats_784_ = lean_ctor_get(v_toCold_771_, 6);
v_maxHeartbeats_785_ = lean_ctor_get(v_toCold_771_, 7);
v_quotContext_786_ = lean_ctor_get(v_toCold_771_, 8);
v_currMacroScope_787_ = lean_ctor_get(v_toCold_771_, 9);
v_cancelTk_x3f_788_ = lean_ctor_get(v_toCold_771_, 10);
v_inheritedTraceOptions_789_ = lean_ctor_get(v_toCold_771_, 11);
v_isSharedCheck_800_ = !lean_is_exclusive(v_toCold_771_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v_toCold_771_, 5);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_toCold_771_, 4);
lean_dec(v_unused_802_);
v___x_791_ = v_toCold_771_;
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_inheritedTraceOptions_789_);
lean_inc(v_cancelTk_x3f_788_);
lean_inc(v_currMacroScope_787_);
lean_inc(v_quotContext_786_);
lean_inc(v_maxHeartbeats_785_);
lean_inc(v_initHeartbeats_784_);
lean_inc(v_maxRecDepth_783_);
lean_inc(v_options_782_);
lean_inc(v_fileMap_781_);
lean_inc(v_fileName_780_);
lean_dec(v_toCold_771_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 5, v_openDecls_768_);
lean_ctor_set(v___x_791_, 4, v_currNamespace_767_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_fileName_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_fileMap_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_options_782_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_maxRecDepth_783_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_currNamespace_767_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_openDecls_768_);
lean_ctor_set(v_reuseFailAlloc_799_, 6, v_initHeartbeats_784_);
lean_ctor_set(v_reuseFailAlloc_799_, 7, v_maxHeartbeats_785_);
lean_ctor_set(v_reuseFailAlloc_799_, 8, v_quotContext_786_);
lean_ctor_set(v_reuseFailAlloc_799_, 9, v_currMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 10, v_cancelTk_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 11, v_inheritedTraceOptions_789_);
v___x_794_ = v_reuseFailAlloc_799_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_794_);
v___x_796_ = v___x_778_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_currRecDepth_772_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_ref_773_);
lean_ctor_set_uint16(v_reuseFailAlloc_798_, sizeof(void*)*3, v_optionFlags_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*3 + 2, v_suppressElabErrors_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*3 + 3, v_isRecordingDeps_776_);
v___x_796_ = v_reuseFailAlloc_798_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; 
lean_inc(v_a_765_);
v___x_797_ = lean_apply_3(v_act_763_, v___x_796_, v_a_765_, lean_box(0));
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg___boxed(lean_object* v_c_804_, lean_object* v_act_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_804_, v_act_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_object* v_00_u03b1_810_, lean_object* v_c_811_, lean_object* v_act_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_811_, v_act_812_, v_a_813_, v_a_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___boxed(lean_object* v_00_u03b1_817_, lean_object* v_c_818_, lean_object* v_act_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(v_00_u03b1_817_, v_c_818_, v_act_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(lean_object* v___x_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_bs_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_828_ == 0)
{
lean_dec(v___x_824_);
return v_bs_827_;
}
else
{
lean_object* v_v_829_; lean_object* v___x_830_; lean_object* v_bs_x27_831_; lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v_v_829_ = lean_array_uget(v_bs_827_, v_i_826_);
v___x_830_ = lean_unsigned_to_nat(0u);
v_bs_x27_831_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_830_);
lean_inc(v___x_824_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_824_);
lean_ctor_set(v___x_832_, 1, v_v_829_);
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_add(v_i_826_, v___x_833_);
v___x_835_ = lean_array_uset(v_bs_x27_831_, v_i_826_, v___x_832_);
v_i_826_ = v___x_834_;
v_bs_827_ = v___x_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0___boxed(lean_object* v___x_837_, lean_object* v_sz_838_, lean_object* v_i_839_, lean_object* v_bs_840_){
_start:
{
size_t v_sz_boxed_841_; size_t v_i_boxed_842_; lean_object* v_res_843_; 
v_sz_boxed_841_ = lean_unbox_usize(v_sz_838_);
lean_dec(v_sz_838_);
v_i_boxed_842_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_837_, v_sz_boxed_841_, v_i_boxed_842_, v_bs_840_);
return v_res_843_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Array_instInhabited___redArg();
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(lean_object* v___x_845_, lean_object* v_inPackage_846_, lean_object* v_env_847_, lean_object* v_range_848_, lean_object* v_b_849_, lean_object* v_i_850_){
_start:
{
lean_object* v_stop_851_; lean_object* v_step_852_; lean_object* v_a_854_; uint8_t v___x_857_; 
v_stop_851_ = lean_ctor_get(v_range_848_, 1);
v_step_852_ = lean_ctor_get(v_range_848_, 2);
v___x_857_ = lean_nat_dec_lt(v_i_850_, v_stop_851_);
if (v___x_857_ == 0)
{
lean_dec(v_i_850_);
lean_dec_ref(v_inPackage_846_);
return v_b_849_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_array_get_borrowed(v___x_858_, v___x_845_, v_i_850_);
lean_inc_ref(v_inPackage_846_);
lean_inc(v___x_859_);
v___x_860_ = lean_apply_1(v_inPackage_846_, v___x_859_);
v___x_861_ = lean_unbox(v___x_860_);
if (v___x_861_ == 0)
{
v_a_854_ = v_b_849_;
goto v___jp_853_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_862_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_863_ = l_Lean_Doc_deferredCheckExt;
v___x_864_ = 0;
v___x_865_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_862_, v___x_863_, v_env_847_, v_i_850_, v___x_864_);
v_sz_866_ = lean_array_size(v___x_865_);
v___x_867_ = ((size_t)0ULL);
lean_inc(v___x_859_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_859_, v_sz_866_, v___x_867_, v___x_865_);
v___x_869_ = l_Array_append___redArg(v_b_849_, v___x_868_);
lean_dec_ref(v___x_868_);
v_a_854_ = v___x_869_;
goto v___jp_853_;
}
}
v___jp_853_:
{
lean_object* v___x_855_; 
v___x_855_ = lean_nat_add(v_i_850_, v_step_852_);
lean_dec(v_i_850_);
v_b_849_ = v_a_854_;
v_i_850_ = v___x_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___boxed(lean_object* v___x_870_, lean_object* v_inPackage_871_, lean_object* v_env_872_, lean_object* v_range_873_, lean_object* v_b_874_, lean_object* v_i_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_870_, v_inPackage_871_, v_env_872_, v_range_873_, v_b_874_, v_i_875_);
lean_dec_ref(v_range_873_);
lean_dec_ref(v_env_872_);
lean_dec_ref(v___x_870_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(lean_object* v_env_879_, lean_object* v_inPackage_880_){
_start:
{
lean_object* v___x_881_; lean_object* v_out_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v_out_882_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0));
v___x_883_ = l_Lean_Environment_header(v_env_879_);
v___x_884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_883_);
v___x_885_ = lean_array_get_size(v___x_884_);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_887_, 0, v___x_881_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
lean_inc_ref(v_inPackage_880_);
v___x_888_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_884_, v_inPackage_880_, v_env_879_, v___x_887_, v_out_882_, v___x_881_);
lean_dec_ref_known(v___x_887_, 3);
lean_dec_ref(v___x_884_);
v___x_889_ = l_Lean_Environment_mainModule(v_env_879_);
lean_inc(v___x_889_);
v___x_890_ = lean_apply_1(v_inPackage_880_, v___x_889_);
v___x_891_ = lean_unbox(v___x_890_);
if (v___x_891_ == 0)
{
lean_dec(v___x_889_);
lean_dec_ref(v_env_879_);
return v___x_888_;
}
else
{
lean_object* v___x_892_; lean_object* v_toEnvExtension_893_; lean_object* v_asyncMode_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_892_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_893_ = lean_ctor_get(v___x_892_, 0);
v_asyncMode_894_ = lean_ctor_get(v_toEnvExtension_893_, 2);
v___x_895_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_896_ = lean_box(0);
v___x_897_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_895_, v___x_892_, v_env_879_, v_asyncMode_894_, v___x_896_);
v_sz_898_ = lean_array_size(v___x_897_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_889_, v_sz_898_, v___x_899_, v___x_897_);
v___x_901_ = l_Array_append___redArg(v___x_888_, v___x_900_);
lean_dec_ref(v___x_900_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(lean_object* v___x_902_, lean_object* v_inPackage_903_, lean_object* v_env_904_, lean_object* v_range_905_, lean_object* v_b_906_, lean_object* v_i_907_, lean_object* v_hs_908_, lean_object* v_hl_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_902_, v_inPackage_903_, v_env_904_, v_range_905_, v_b_906_, v_i_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___boxed(lean_object* v___x_911_, lean_object* v_inPackage_912_, lean_object* v_env_913_, lean_object* v_range_914_, lean_object* v_b_915_, lean_object* v_i_916_, lean_object* v_hs_917_, lean_object* v_hl_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(v___x_911_, v_inPackage_912_, v_env_913_, v_range_914_, v_b_915_, v_i_916_, v_hs_917_, v_hl_918_);
lean_dec_ref(v_range_914_);
lean_dec_ref(v_env_913_);
lean_dec_ref(v___x_911_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(lean_object* v_as_920_, size_t v_i_921_, size_t v_stop_922_, lean_object* v_b_923_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = lean_usize_dec_eq(v_i_921_, v_stop_922_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; size_t v___x_927_; size_t v___x_928_; 
v___x_925_ = lean_array_uget_borrowed(v_as_920_, v_i_921_);
lean_inc(v___x_925_);
v___x_926_ = l_Lean_NameSet_insert(v_b_923_, v___x_925_);
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_921_, v___x_927_);
v_i_921_ = v___x_928_;
v_b_923_ = v___x_926_;
goto _start;
}
else
{
return v_b_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3___boxed(lean_object* v_as_930_, lean_object* v_i_931_, lean_object* v_stop_932_, lean_object* v_b_933_){
_start:
{
size_t v_i_boxed_934_; size_t v_stop_boxed_935_; lean_object* v_res_936_; 
v_i_boxed_934_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_stop_boxed_935_ = lean_unbox_usize(v_stop_932_);
lean_dec(v_stop_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_as_930_, v_i_boxed_934_, v_stop_boxed_935_, v_b_933_);
lean_dec_ref(v_as_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(lean_object* v___y_937_, lean_object* v_as_938_, size_t v_i_939_, size_t v_stop_940_, lean_object* v_b_941_){
_start:
{
lean_object* v___y_943_; uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_eq(v_i_939_, v_stop_940_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_array_uget_borrowed(v_as_938_, v_i_939_);
v___x_949_ = l_Lean_NameSet_contains(v___y_937_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_inc(v___x_948_);
v___x_950_ = lean_array_push(v_b_941_, v___x_948_);
v___y_943_ = v___x_950_;
goto v___jp_942_;
}
else
{
v___y_943_ = v_b_941_;
goto v___jp_942_;
}
}
else
{
return v_b_941_;
}
v___jp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_939_, v___x_944_);
v_i_939_ = v___x_945_;
v_b_941_ = v___y_943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1___boxed(lean_object* v___y_951_, lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_stop_954_, lean_object* v_b_955_){
_start:
{
size_t v_i_boxed_956_; size_t v_stop_boxed_957_; lean_object* v_res_958_; 
v_i_boxed_956_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_stop_boxed_957_ = lean_unbox_usize(v_stop_954_);
lean_dec(v_stop_954_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_951_, v_as_952_, v_i_boxed_956_, v_stop_boxed_957_, v_b_955_);
lean_dec_ref(v_as_952_);
lean_dec(v___y_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
if (lean_obj_tag(v_a_959_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = l_List_reverse___redArg(v_a_960_);
return v___x_961_;
}
else
{
lean_object* v_head_962_; lean_object* v_tail_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v_head_962_ = lean_ctor_get(v_a_959_, 0);
v_tail_963_ = lean_ctor_get(v_a_959_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v_a_959_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_tail_963_);
lean_inc(v_head_962_);
lean_dec(v_a_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = l_Lean_MessageData_ofName(v_head_962_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_a_960_);
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_a_960_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v_a_959_ = v_tail_963_;
v_a_960_ = v___x_969_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(lean_object* v_shouldCheck_987_, lean_object* v_val_988_, lean_object* v___x_989_, lean_object* v___y_990_, lean_object* v_as_991_, size_t v_sz_992_, size_t v_i_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_a_999_; uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_lt(v_i_993_, v_sz_992_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec_ref(v_shouldCheck_987_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_b_994_);
return v___x_1004_;
}
else
{
lean_object* v_a_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1096_; 
v_a_1005_ = lean_array_uget(v_as_991_, v_i_993_);
v_fst_1006_ = lean_ctor_get(v_a_1005_, 0);
v_snd_1007_ = lean_ctor_get(v_a_1005_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1009_ = v_a_1005_;
v_isShared_1010_ = v_isSharedCheck_1096_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1007_);
lean_inc(v_fst_1006_);
lean_dec(v_a_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1096_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v_val_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_shouldCheck_987_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v_snd_1007_);
v___x_1043_ = lean_apply_4(v_shouldCheck_987_, v_snd_1007_, v___y_995_, v___y_996_, lean_box(0));
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; uint8_t v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = lean_unbox(v_a_1044_);
lean_dec(v_a_1044_);
if (v___x_1045_ == 0)
{
lean_del_object(v___x_1009_);
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
v_a_999_ = v_b_994_;
goto v___jp_998_;
}
else
{
lean_object* v_imports_1046_; lean_object* v_check_1047_; lean_object* v___y_1049_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_imports_1046_ = lean_ctor_get(v_snd_1007_, 3);
v_check_1047_ = lean_ctor_get(v_snd_1007_, 7);
v___x_1078_ = lean_array_get_size(v_imports_1046_);
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8));
v___x_1080_ = lean_nat_dec_lt(v___x_1042_, v___x_1078_);
if (v___x_1080_ == 0)
{
v___y_1049_ = v___x_1079_;
goto v___jp_1048_;
}
else
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_nat_dec_le(v___x_1078_, v___x_1078_);
if (v___x_1081_ == 0)
{
if (v___x_1080_ == 0)
{
v___y_1049_ = v___x_1079_;
goto v___jp_1048_;
}
else
{
size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = lean_usize_of_nat(v___x_1078_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_990_, v_imports_1046_, v___x_1082_, v___x_1083_, v___x_1079_);
v___y_1049_ = v___x_1084_;
goto v___jp_1048_;
}
}
else
{
size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = lean_usize_of_nat(v___x_1078_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_990_, v_imports_1046_, v___x_1085_, v___x_1086_, v___x_1079_);
v___y_1049_ = v___x_1087_;
goto v___jp_1048_;
}
}
v___jp_1048_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v___y_1049_);
v___x_1051_ = lean_nat_dec_eq(v___x_1050_, v___x_1042_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_del_object(v___x_1009_);
v___x_1052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5);
v___x_1053_ = lean_array_to_list(v___y_1049_);
v___x_1054_ = lean_box(0);
v___x_1055_ = l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(v___x_1053_, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_ofList(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_snd_1007_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_fst_1006_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_array_push(v_b_994_, v___x_1061_);
v_a_999_ = v___x_1062_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref(v___y_1049_);
v___x_1063_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1047_);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_988_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
goto v___jp_1011_;
}
else
{
lean_object* v_val_1065_; 
lean_del_object(v___x_1009_);
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v_val_1033_ = v_val_1065_;
v___y_1034_ = v___y_995_;
v___y_1035_ = v___y_996_;
goto v___jp_1032_;
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v___x_1064_);
v___x_1066_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_989_, v___x_1063_);
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1066_) == 1)
{
lean_object* v_val_1067_; lean_object* v___x_1068_; 
lean_del_object(v___x_1009_);
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_val_1067_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v_val_1033_ = v_a_1069_;
v___y_1034_ = v___y_995_;
v___y_1035_ = v___y_996_;
goto v___jp_1032_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v_b_994_);
lean_dec_ref(v_shouldCheck_987_);
v_a_1070_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1068_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_dec(v___x_1066_);
goto v___jp_1011_;
}
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1009_);
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v_b_994_);
lean_dec_ref(v_shouldCheck_987_);
v_a_1088_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1043_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1043_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_1011_:
{
lean_object* v_check_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v_check_1012_ = lean_ctor_get(v_snd_1007_, 7);
v___x_1013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1);
v___x_1014_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1012_);
v___x_1015_ = l_Lean_MessageData_ofName(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1018_);
lean_ctor_set(v___x_1009_, 0, v_snd_1007_);
v___x_1020_ = v___x_1009_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_snd_1007_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_fst_1006_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_array_push(v_b_994_, v___x_1021_);
v_a_999_ = v___x_1022_;
goto v___jp_998_;
}
}
v___jp_1024_:
{
if (v___y_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = l_Lean_Exception_toMessageData(v___y_1025_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_snd_1007_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_fst_1006_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_array_push(v_b_994_, v___x_1029_);
v_a_999_ = v___x_1030_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1031_; 
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v_b_994_);
lean_dec_ref(v_shouldCheck_987_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1025_);
return v___x_1031_;
}
}
v___jp_1032_:
{
lean_object* v_check_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_check_1036_ = lean_ctor_get(v_snd_1007_, 7);
lean_inc(v_check_1036_);
v___x_1037_ = lean_apply_1(v_val_1033_, v_check_1036_);
lean_inc(v_snd_1007_);
v___x_1038_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_snd_1007_, v___x_1037_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
v_a_999_ = v_b_994_;
goto v___jp_998_;
}
else
{
lean_object* v_a_1039_; uint8_t v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_Lean_Exception_isInterrupt(v_a_1039_);
if (v___x_1040_ == 0)
{
uint8_t v___x_1041_; 
lean_inc(v_a_1039_);
v___x_1041_ = l_Lean_Exception_isRuntime(v_a_1039_);
v___y_1025_ = v_a_1039_;
v___y_1026_ = v___x_1041_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v_a_1039_;
v___y_1026_ = v___x_1040_;
goto v___jp_1024_;
}
}
}
}
}
v___jp_998_:
{
size_t v___x_1000_; size_t v___x_1001_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_993_, v___x_1000_);
v_i_993_ = v___x_1001_;
v_b_994_ = v_a_999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___boxed(lean_object* v_shouldCheck_1097_, lean_object* v_val_1098_, lean_object* v___x_1099_, lean_object* v___y_1100_, lean_object* v_as_1101_, lean_object* v_sz_1102_, lean_object* v_i_1103_, lean_object* v_b_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1102_);
lean_dec(v_sz_1102_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1097_, v_val_1098_, v___x_1099_, v___y_1100_, v_as_1101_, v_sz_boxed_1108_, v_i_boxed_1109_, v_b_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_as_1101_);
lean_dec(v___y_1100_);
lean_dec(v___x_1099_);
lean_dec(v_val_1098_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run(lean_object* v_inPackage_1113_, lean_object* v_shouldCheck_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_env_1120_; lean_object* v___x_1121_; lean_object* v_toEnvExtension_1122_; lean_object* v_asyncMode_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___y_1133_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1118_ = lean_box(1);
v___x_1119_ = lean_st_ref_get(v_a_1116_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref_n(v_env_1120_, 2);
lean_dec(v___x_1119_);
v___x_1121_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_1122_ = lean_ctor_get(v___x_1121_, 0);
v_asyncMode_1123_ = lean_ctor_get(v_toEnvExtension_1122_, 2);
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1118_, v___x_1121_, v_env_1120_, v_asyncMode_1123_, v___x_1124_);
v___x_1126_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_1127_ = lean_st_ref_get(v___x_1126_);
v___x_1128_ = l_Lean_NameSet_empty;
v___x_1129_ = l_Lean_Environment_header(v_env_1120_);
v___x_1130_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_array_get_size(v___x_1130_);
v___x_1140_ = lean_nat_dec_lt(v___x_1131_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_dec_ref(v___x_1130_);
v___y_1133_ = v___x_1128_;
goto v___jp_1132_;
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_le(v___x_1139_, v___x_1139_);
if (v___x_1141_ == 0)
{
if (v___x_1140_ == 0)
{
lean_dec_ref(v___x_1130_);
v___y_1133_ = v___x_1128_;
goto v___jp_1132_;
}
else
{
size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = lean_usize_of_nat(v___x_1139_);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v___x_1130_, v___x_1142_, v___x_1143_, v___x_1128_);
lean_dec_ref(v___x_1130_);
v___y_1133_ = v___x_1144_;
goto v___jp_1132_;
}
}
else
{
size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = lean_usize_of_nat(v___x_1139_);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v___x_1130_, v___x_1145_, v___x_1146_, v___x_1128_);
lean_dec_ref(v___x_1130_);
v___y_1133_ = v___x_1147_;
goto v___jp_1132_;
}
}
v___jp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1134_ = ((lean_object*)(l_Lean_Doc_DeferredCheck_run___closed__0));
v___x_1135_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(v_env_1120_, v_inPackage_1113_);
v_sz_1136_ = lean_array_size(v___x_1135_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1114_, v___x_1127_, v___x_1125_, v___y_1133_, v___x_1135_, v_sz_1136_, v___x_1137_, v___x_1134_, v_a_1115_, v_a_1116_);
lean_dec_ref(v___x_1135_);
lean_dec(v___y_1133_);
lean_dec(v___x_1125_);
lean_dec(v___x_1127_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run___boxed(lean_object* v_inPackage_1148_, lean_object* v_shouldCheck_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Doc_DeferredCheck_run(v_inPackage_1148_, v_shouldCheck_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1153_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_linter_doc_deferred = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_linter_doc_deferred);
lean_dec_ref(res);
res = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Doc_DeferredCheck_handlerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Doc_DeferredCheck_handlerExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Doc_DeferredCheck_builtinHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Doc_DeferredCheck_builtinHandlers);
lean_dec_ref(res);
res = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
}
#ifdef __cplusplus
}
#endif
