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
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_Doc_deferredCheckExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "invalid `deferred_doc_check` syntax"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `deferred_doc_check`, must be global"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
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
v___x_196_ = lean_st_ref_set(v___x_193_, v___x_195_);
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
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_207_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_225_; lean_object* v_env_226_; lean_object* v_options_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_225_ = lean_st_ref_get(v___y_223_);
v_env_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_226_);
lean_dec(v___x_225_);
v_options_227_ = lean_ctor_get(v___y_222_, 2);
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_227_);
v___x_230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_230_, 0, v_env_226_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set(v___x_230_, 3, v_options_227_);
v___x_231_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_msgData_221_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_ref_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_ref_242_ = lean_ctor_get(v___y_239_, 5);
v___x_243_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_238_, v___y_239_, v___y_240_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc(v_ref_242_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_242_);
lean_ctor_set(v___x_248_, 1, v_a_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 1);
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object* v_x_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_262_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v_x_258_, 1);
v___x_263_ = l_Lean_stringToMessageData(v_a_262_);
v___x_264_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_263_, v___y_259_, v___y_260_);
return v___x_264_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v_x_258_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v_x_258_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v_x_258_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 0);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_box(0);
v___x_279_ = l_Lean_Elab_abortCommandExceptionId;
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(lean_object* v_typeName_286_, lean_object* v_constName_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v_env_292_; uint8_t v___x_293_; 
v___x_291_ = lean_st_ref_get(v___y_289_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
lean_dec(v___x_291_);
lean_inc(v_constName_287_);
v___x_293_ = lean_has_compile_error(v_env_292_, v_constName_287_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = lean_st_ref_get(v___y_289_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v_options_296_ = lean_ctor_get(v___y_288_, 2);
v___x_297_ = l_Lean_Environment_evalConstCheck___redArg(v_env_295_, v_options_296_, v_typeName_286_, v_constName_287_);
v___x_298_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_297_, v___y_288_, v___y_289_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; lean_object* v_env_301_; lean_object* v_options_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v___x_299_, 1);
v___x_300_ = lean_st_ref_get(v___y_289_);
v_env_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_ref(v_env_301_);
lean_dec(v___x_300_);
v_options_302_ = lean_ctor_get(v___y_288_, 2);
v___x_303_ = l_Lean_Environment_evalConstCheck___redArg(v_env_301_, v_options_302_, v_typeName_286_, v_constName_287_);
v___x_304_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_303_, v___y_288_, v___y_289_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_constName_287_);
lean_dec(v_typeName_286_);
v_a_305_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_299_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_299_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_313_, lean_object* v_constName_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_313_, v_constName_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(lean_object* v_declName_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1));
v___x_329_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v___x_328_, v_declName_324_, v_a_325_, v_a_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___boxed(lean_object* v_declName_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_declName_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_object* v_00_u03b1_345_, lean_object* v_typeName_346_, lean_object* v_constName_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_346_, v_constName_347_, v___y_348_, v___y_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_352_, lean_object* v_typeName_353_, lean_object* v_constName_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(v_00_u03b1_352_, v_typeName_353_, v_constName_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_360_, v___y_361_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_365_, v_x_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_377_, v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_383_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_decl_401_, lean_object* v_stx_402_, uint8_t v_kind_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_key_408_; lean_object* v___y_409_; uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 0;
v___x_489_ = l_Lean_instBEqAttributeKind_beq(v_kind_403_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec_ref(v___x_398_);
lean_dec(v___x_397_);
v___x_490_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__9_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_491_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_490_, v___y_404_, v___y_405_);
return v___x_491_;
}
else
{
goto v___jp_436_;
}
v___jp_407_:
{
lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_traceState_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_434_; 
v___x_410_ = lean_st_ref_take(v___y_409_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_410_, 1);
v_ngen_413_ = lean_ctor_get(v___x_410_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_410_, 3);
v_traceState_415_ = lean_ctor_get(v___x_410_, 4);
v_messages_416_ = lean_ctor_get(v___x_410_, 6);
v_infoState_417_ = lean_ctor_get(v___x_410_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_410_, 8);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_410_, 5);
lean_dec(v_unused_435_);
v___x_420_ = v___x_410_;
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_traceState_415_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_410_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v_toEnvExtension_423_; lean_object* v_asyncMode_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_422_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_423_ = lean_ctor_get(v___x_422_, 0);
v_asyncMode_424_ = lean_ctor_get(v_toEnvExtension_423_, 2);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_key_408_);
lean_ctor_set(v___x_425_, 1, v_decl_401_);
v___x_426_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_422_, v_env_411_, v___x_425_, v_asyncMode_424_, v___x_397_);
v___x_427_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 5, v___x_427_);
lean_ctor_set(v___x_420_, 0, v___x_426_);
v___x_429_ = v___x_420_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_traceState_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_snapshotTasks_418_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_st_ref_set(v___y_409_, v___x_429_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
v___jp_436_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_439_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_440_ = l_Lean_Name_mkStr4(v___x_398_, v___x_437_, v___x_438_, v___x_439_);
lean_inc(v_stx_402_);
v___x_441_ = l_Lean_Syntax_isOfKind(v_stx_402_, v___x_440_);
lean_dec(v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_442_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_443_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_442_, v___y_404_, v___y_405_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = l_Lean_Syntax_getArg(v_stx_402_, v___x_399_);
v___x_453_ = l_Lean_Syntax_matchesIdent(v___x_452_, v___x_400_);
lean_dec(v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v_stx_402_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_454_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_455_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_454_, v___y_404_, v___y_405_);
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = l_Lean_Syntax_getArg(v_stx_402_, v___x_464_);
lean_dec(v_stx_402_);
lean_inc(v___x_465_);
v___x_466_ = l_Lean_Syntax_matchesNull(v___x_465_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v___x_465_);
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v___x_467_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_468_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_467_, v___y_404_, v___y_405_);
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = l_Lean_Syntax_getArg(v___x_465_, v___x_399_);
lean_dec(v___x_465_);
v___x_478_ = l_Lean_realizeGlobalConstNoOverload(v___x_477_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_key_408_ = v_a_479_;
v___y_409_ = v___y_405_;
goto v___jp_407_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_decl_401_);
lean_dec(v___x_397_);
v_a_480_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_478_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v_decl_496_, lean_object* v_stx_497_, lean_object* v_kind_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v_kind_boxed_502_; lean_object* v_res_503_; 
v_kind_boxed_502_ = lean_unbox(v_kind_498_);
v_res_503_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_492_, v___x_493_, v___x_494_, v___x_495_, v_decl_496_, v_stx_497_, v_kind_boxed_502_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___x_495_);
lean_dec(v___x_494_);
return v_res_503_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_510_, lean_object* v_decl_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_516_ = l_Lean_MessageData_ofName(v___x_510_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_519_, v___y_512_, v___y_513_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_521_, lean_object* v_decl_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_521_, v_decl_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v_decl_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_621_ = l_Lean_registerBuiltinAttribute(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
return v_res_623_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v_decl_636_, lean_object* v_stx_637_, uint8_t v_kind_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_key_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 0;
v___x_707_ = l_Lean_instBEqAttributeKind_beq(v_kind_638_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_stx_637_);
lean_dec(v_decl_636_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
v___x_708_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_709_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_708_, v___y_639_, v___y_640_);
return v___x_709_;
}
else
{
goto v___jp_654_;
}
v___jp_642_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_647_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___x_633_, v___x_646_);
v___x_648_ = lean_box(0);
v___x_649_ = l_Lean_Expr_const___override(v___x_647_, v___x_648_);
v___x_650_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_key_643_);
lean_inc(v_decl_636_);
v___x_651_ = l_Lean_Expr_const___override(v_decl_636_, v___x_648_);
v___x_652_ = l_Lean_mkAppB(v___x_649_, v___x_650_, v___x_651_);
v___x_653_ = l_Lean_declareBuiltin(v_decl_636_, v___x_652_, v___y_644_, v___y_645_);
return v___x_653_;
}
v___jp_654_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
lean_inc_ref(v___x_631_);
v___x_658_ = l_Lean_Name_mkStr4(v___x_631_, v___x_655_, v___x_656_, v___x_657_);
lean_inc(v_stx_637_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_stx_637_, v___x_658_);
lean_dec(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_stx_637_);
lean_dec(v_decl_636_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
v___x_660_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_661_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_660_, v___y_639_, v___y_640_);
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = l_Lean_Syntax_getArg(v_stx_637_, v___x_634_);
v___x_671_ = l_Lean_Syntax_matchesIdent(v___x_670_, v___x_635_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_stx_637_);
lean_dec(v_decl_636_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
v___x_672_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_673_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_672_, v___y_639_, v___y_640_);
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = l_Lean_Syntax_getArg(v_stx_637_, v___x_682_);
lean_dec(v_stx_637_);
lean_inc(v___x_683_);
v___x_684_ = l_Lean_Syntax_matchesNull(v___x_683_, v___x_682_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v___x_683_);
lean_dec(v_decl_636_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
v___x_685_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_686_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_685_, v___y_639_, v___y_640_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l_Lean_Syntax_getArg(v___x_683_, v___x_634_);
lean_dec(v___x_683_);
v___x_696_ = l_Lean_realizeGlobalConstNoOverload(v___x_695_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v_key_643_ = v_a_697_;
v___y_644_ = v___y_639_;
v___y_645_ = v___y_640_;
goto v___jp_642_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_decl_636_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
v_a_698_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_decl_715_, lean_object* v_stx_716_, lean_object* v_kind_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint8_t v_kind_boxed_721_; lean_object* v_res_722_; 
v_kind_boxed_721_ = lean_unbox(v_kind_717_);
v_res_722_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(v___x_710_, v___x_711_, v___x_712_, v___x_713_, v___x_714_, v_decl_715_, v_stx_716_, v_kind_boxed_721_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___x_714_);
lean_dec(v___x_713_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_758_ = l_Lean_registerBuiltinAttribute(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(lean_object* v_c_761_, lean_object* v_act_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_fileName_766_; lean_object* v_fileMap_767_; lean_object* v_currRecDepth_768_; lean_object* v_maxRecDepth_769_; lean_object* v_ref_770_; lean_object* v_initHeartbeats_771_; lean_object* v_maxHeartbeats_772_; lean_object* v_quotContext_773_; lean_object* v_currMacroScope_774_; uint8_t v_diag_775_; lean_object* v_cancelTk_x3f_776_; uint8_t v_suppressElabErrors_777_; lean_object* v_inheritedTraceOptions_778_; lean_object* v_currNamespace_779_; lean_object* v_openDecls_780_; lean_object* v_options_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_fileName_766_ = lean_ctor_get(v_a_763_, 0);
v_fileMap_767_ = lean_ctor_get(v_a_763_, 1);
v_currRecDepth_768_ = lean_ctor_get(v_a_763_, 3);
v_maxRecDepth_769_ = lean_ctor_get(v_a_763_, 4);
v_ref_770_ = lean_ctor_get(v_a_763_, 5);
v_initHeartbeats_771_ = lean_ctor_get(v_a_763_, 8);
v_maxHeartbeats_772_ = lean_ctor_get(v_a_763_, 9);
v_quotContext_773_ = lean_ctor_get(v_a_763_, 10);
v_currMacroScope_774_ = lean_ctor_get(v_a_763_, 11);
v_diag_775_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*14);
v_cancelTk_x3f_776_ = lean_ctor_get(v_a_763_, 12);
v_suppressElabErrors_777_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_778_ = lean_ctor_get(v_a_763_, 13);
v_currNamespace_779_ = lean_ctor_get(v_c_761_, 4);
v_openDecls_780_ = lean_ctor_get(v_c_761_, 5);
v_options_781_ = lean_ctor_get(v_c_761_, 6);
lean_inc_ref(v_inheritedTraceOptions_778_);
lean_inc(v_cancelTk_x3f_776_);
lean_inc(v_currMacroScope_774_);
lean_inc(v_quotContext_773_);
lean_inc(v_maxHeartbeats_772_);
lean_inc(v_initHeartbeats_771_);
lean_inc(v_openDecls_780_);
lean_inc(v_currNamespace_779_);
lean_inc(v_ref_770_);
lean_inc(v_maxRecDepth_769_);
lean_inc(v_currRecDepth_768_);
lean_inc_ref(v_options_781_);
lean_inc_ref(v_fileMap_767_);
lean_inc_ref(v_fileName_766_);
v___x_782_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_782_, 0, v_fileName_766_);
lean_ctor_set(v___x_782_, 1, v_fileMap_767_);
lean_ctor_set(v___x_782_, 2, v_options_781_);
lean_ctor_set(v___x_782_, 3, v_currRecDepth_768_);
lean_ctor_set(v___x_782_, 4, v_maxRecDepth_769_);
lean_ctor_set(v___x_782_, 5, v_ref_770_);
lean_ctor_set(v___x_782_, 6, v_currNamespace_779_);
lean_ctor_set(v___x_782_, 7, v_openDecls_780_);
lean_ctor_set(v___x_782_, 8, v_initHeartbeats_771_);
lean_ctor_set(v___x_782_, 9, v_maxHeartbeats_772_);
lean_ctor_set(v___x_782_, 10, v_quotContext_773_);
lean_ctor_set(v___x_782_, 11, v_currMacroScope_774_);
lean_ctor_set(v___x_782_, 12, v_cancelTk_x3f_776_);
lean_ctor_set(v___x_782_, 13, v_inheritedTraceOptions_778_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*14, v_diag_775_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*14 + 1, v_suppressElabErrors_777_);
lean_inc(v_a_764_);
v___x_783_ = lean_apply_3(v_act_762_, v___x_782_, v_a_764_, lean_box(0));
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg___boxed(lean_object* v_c_784_, lean_object* v_act_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_784_, v_act_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec_ref(v_c_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_object* v_00_u03b1_790_, lean_object* v_c_791_, lean_object* v_act_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_791_, v_act_792_, v_a_793_, v_a_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___boxed(lean_object* v_00_u03b1_797_, lean_object* v_c_798_, lean_object* v_act_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(v_00_u03b1_797_, v_c_798_, v_act_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec_ref(v_c_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(lean_object* v___x_804_, size_t v_sz_805_, size_t v_i_806_, lean_object* v_bs_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_806_, v_sz_805_);
if (v___x_808_ == 0)
{
lean_dec(v___x_804_);
return v_bs_807_;
}
else
{
lean_object* v_v_809_; lean_object* v___x_810_; lean_object* v_bs_x27_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_v_809_ = lean_array_uget(v_bs_807_, v_i_806_);
v___x_810_ = lean_unsigned_to_nat(0u);
v_bs_x27_811_ = lean_array_uset(v_bs_807_, v_i_806_, v___x_810_);
lean_inc(v___x_804_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_804_);
lean_ctor_set(v___x_812_, 1, v_v_809_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_add(v_i_806_, v___x_813_);
v___x_815_ = lean_array_uset(v_bs_x27_811_, v_i_806_, v___x_812_);
v_i_806_ = v___x_814_;
v_bs_807_ = v___x_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0___boxed(lean_object* v___x_817_, lean_object* v_sz_818_, lean_object* v_i_819_, lean_object* v_bs_820_){
_start:
{
size_t v_sz_boxed_821_; size_t v_i_boxed_822_; lean_object* v_res_823_; 
v_sz_boxed_821_ = lean_unbox_usize(v_sz_818_);
lean_dec(v_sz_818_);
v_i_boxed_822_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_817_, v_sz_boxed_821_, v_i_boxed_822_, v_bs_820_);
return v_res_823_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Array_instInhabited(lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(lean_object* v___x_825_, lean_object* v_inPackage_826_, lean_object* v_env_827_, lean_object* v_range_828_, lean_object* v_b_829_, lean_object* v_i_830_){
_start:
{
lean_object* v_stop_831_; lean_object* v_step_832_; lean_object* v_a_834_; uint8_t v___x_837_; 
v_stop_831_ = lean_ctor_get(v_range_828_, 1);
v_step_832_ = lean_ctor_get(v_range_828_, 2);
v___x_837_ = lean_nat_dec_lt(v_i_830_, v_stop_831_);
if (v___x_837_ == 0)
{
lean_dec(v_i_830_);
lean_dec_ref(v_inPackage_826_);
return v_b_829_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_box(0);
v___x_839_ = lean_array_get_borrowed(v___x_838_, v___x_825_, v_i_830_);
lean_inc_ref(v_inPackage_826_);
lean_inc(v___x_839_);
v___x_840_ = lean_apply_1(v_inPackage_826_, v___x_839_);
v___x_841_ = lean_unbox(v___x_840_);
if (v___x_841_ == 0)
{
v_a_834_ = v_b_829_;
goto v___jp_833_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; size_t v_sz_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_842_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_843_ = l_Lean_Doc_deferredCheckExt;
v___x_844_ = 0;
v___x_845_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_842_, v___x_843_, v_env_827_, v_i_830_, v___x_844_);
v_sz_846_ = lean_array_size(v___x_845_);
v___x_847_ = ((size_t)0ULL);
lean_inc(v___x_839_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_839_, v_sz_846_, v___x_847_, v___x_845_);
v___x_849_ = l_Array_append___redArg(v_b_829_, v___x_848_);
lean_dec_ref(v___x_848_);
v_a_834_ = v___x_849_;
goto v___jp_833_;
}
}
v___jp_833_:
{
lean_object* v___x_835_; 
v___x_835_ = lean_nat_add(v_i_830_, v_step_832_);
lean_dec(v_i_830_);
v_b_829_ = v_a_834_;
v_i_830_ = v___x_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___boxed(lean_object* v___x_850_, lean_object* v_inPackage_851_, lean_object* v_env_852_, lean_object* v_range_853_, lean_object* v_b_854_, lean_object* v_i_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_850_, v_inPackage_851_, v_env_852_, v_range_853_, v_b_854_, v_i_855_);
lean_dec_ref(v_range_853_);
lean_dec_ref(v_env_852_);
lean_dec_ref(v___x_850_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(lean_object* v_env_859_, lean_object* v_inPackage_860_){
_start:
{
lean_object* v___x_861_; lean_object* v_out_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v_out_862_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0));
v___x_863_ = l_Lean_Environment_header(v_env_859_);
v___x_864_ = l_Lean_EnvironmentHeader_moduleNames(v___x_863_);
v___x_865_ = lean_array_get_size(v___x_864_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_861_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_inc_ref(v_inPackage_860_);
v___x_868_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_864_, v_inPackage_860_, v_env_859_, v___x_867_, v_out_862_, v___x_861_);
lean_dec_ref_known(v___x_867_, 3);
lean_dec_ref(v___x_864_);
v___x_869_ = l_Lean_Environment_mainModule(v_env_859_);
lean_inc(v___x_869_);
v___x_870_ = lean_apply_1(v_inPackage_860_, v___x_869_);
v___x_871_ = lean_unbox(v___x_870_);
if (v___x_871_ == 0)
{
lean_dec(v___x_869_);
lean_dec_ref(v_env_859_);
return v___x_868_;
}
else
{
lean_object* v___x_872_; lean_object* v_toEnvExtension_873_; lean_object* v_asyncMode_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_872_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_873_ = lean_ctor_get(v___x_872_, 0);
v_asyncMode_874_ = lean_ctor_get(v_toEnvExtension_873_, 2);
v___x_875_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_876_ = lean_box(0);
v___x_877_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_875_, v___x_872_, v_env_859_, v_asyncMode_874_, v___x_876_);
v_sz_878_ = lean_array_size(v___x_877_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_869_, v_sz_878_, v___x_879_, v___x_877_);
v___x_881_ = l_Array_append___redArg(v___x_868_, v___x_880_);
lean_dec_ref(v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(lean_object* v___x_882_, lean_object* v_inPackage_883_, lean_object* v_env_884_, lean_object* v_range_885_, lean_object* v_b_886_, lean_object* v_i_887_, lean_object* v_hs_888_, lean_object* v_hl_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_882_, v_inPackage_883_, v_env_884_, v_range_885_, v_b_886_, v_i_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___boxed(lean_object* v___x_891_, lean_object* v_inPackage_892_, lean_object* v_env_893_, lean_object* v_range_894_, lean_object* v_b_895_, lean_object* v_i_896_, lean_object* v_hs_897_, lean_object* v_hl_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(v___x_891_, v_inPackage_892_, v_env_893_, v_range_894_, v_b_895_, v_i_896_, v_hs_897_, v_hl_898_);
lean_dec_ref(v_range_894_);
lean_dec_ref(v_env_893_);
lean_dec_ref(v___x_891_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(lean_object* v_as_900_, size_t v_i_901_, size_t v_stop_902_, lean_object* v_b_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_eq(v_i_901_, v_stop_902_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; size_t v___x_907_; size_t v___x_908_; 
v___x_905_ = lean_array_uget_borrowed(v_as_900_, v_i_901_);
lean_inc(v___x_905_);
v___x_906_ = l_Lean_NameSet_insert(v_b_903_, v___x_905_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_901_, v___x_907_);
v_i_901_ = v___x_908_;
v_b_903_ = v___x_906_;
goto _start;
}
else
{
return v_b_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3___boxed(lean_object* v_as_910_, lean_object* v_i_911_, lean_object* v_stop_912_, lean_object* v_b_913_){
_start:
{
size_t v_i_boxed_914_; size_t v_stop_boxed_915_; lean_object* v_res_916_; 
v_i_boxed_914_ = lean_unbox_usize(v_i_911_);
lean_dec(v_i_911_);
v_stop_boxed_915_ = lean_unbox_usize(v_stop_912_);
lean_dec(v_stop_912_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_as_910_, v_i_boxed_914_, v_stop_boxed_915_, v_b_913_);
lean_dec_ref(v_as_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(lean_object* v___y_917_, lean_object* v_as_918_, size_t v_i_919_, size_t v_stop_920_, lean_object* v_b_921_){
_start:
{
lean_object* v___y_923_; uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_eq(v_i_919_, v_stop_920_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_uget_borrowed(v_as_918_, v_i_919_);
v___x_929_ = l_Lean_NameSet_contains(v___y_917_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_inc(v___x_928_);
v___x_930_ = lean_array_push(v_b_921_, v___x_928_);
v___y_923_ = v___x_930_;
goto v___jp_922_;
}
else
{
v___y_923_ = v_b_921_;
goto v___jp_922_;
}
}
else
{
return v_b_921_;
}
v___jp_922_:
{
size_t v___x_924_; size_t v___x_925_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_919_, v___x_924_);
v_i_919_ = v___x_925_;
v_b_921_ = v___y_923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1___boxed(lean_object* v___y_931_, lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_stop_934_, lean_object* v_b_935_){
_start:
{
size_t v_i_boxed_936_; size_t v_stop_boxed_937_; lean_object* v_res_938_; 
v_i_boxed_936_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_stop_boxed_937_ = lean_unbox_usize(v_stop_934_);
lean_dec(v_stop_934_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_931_, v_as_932_, v_i_boxed_936_, v_stop_boxed_937_, v_b_935_);
lean_dec_ref(v_as_932_);
lean_dec(v___y_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_List_reverse___redArg(v_a_940_);
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_952_; 
v_head_942_ = lean_ctor_get(v_a_939_, 0);
v_tail_943_ = lean_ctor_get(v_a_939_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_952_ == 0)
{
v___x_945_ = v_a_939_;
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_tail_943_);
lean_inc(v_head_942_);
lean_dec(v_a_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_MessageData_ofName(v_head_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_a_940_);
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_940_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v_a_939_ = v_tail_943_;
v_a_940_ = v___x_949_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(lean_object* v_shouldCheck_967_, lean_object* v_val_968_, lean_object* v___x_969_, lean_object* v___y_970_, lean_object* v_as_971_, size_t v_sz_972_, size_t v_i_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_a_979_; uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_973_, v_sz_972_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v_shouldCheck_967_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_974_);
return v___x_984_;
}
else
{
lean_object* v_a_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1074_; 
v_a_985_ = lean_array_uget(v_as_971_, v_i_973_);
v_fst_986_ = lean_ctor_get(v_a_985_, 0);
v_snd_987_ = lean_ctor_get(v_a_985_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_989_ = v_a_985_;
v_isShared_990_ = v_isSharedCheck_1074_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_inc(v_fst_986_);
lean_dec(v_a_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1074_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___y_992_; uint8_t v___y_993_; lean_object* v___x_1001_; 
lean_inc_ref(v_shouldCheck_967_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v_snd_987_);
v___x_1001_ = lean_apply_4(v_shouldCheck_967_, v_snd_987_, v___y_975_, v___y_976_, lean_box(0));
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; uint8_t v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_unbox(v_a_1002_);
lean_dec(v_a_1002_);
if (v___x_1003_ == 0)
{
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_979_ = v_b_974_;
goto v___jp_978_;
}
else
{
lean_object* v_imports_1004_; lean_object* v_check_1005_; lean_object* v_val_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___x_1025_; lean_object* v___y_1027_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_imports_1004_ = lean_ctor_get(v_snd_987_, 3);
v_check_1005_ = lean_ctor_get(v_snd_987_, 7);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_array_get_size(v_imports_1004_);
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8));
v___x_1058_ = lean_nat_dec_lt(v___x_1025_, v___x_1056_);
if (v___x_1058_ == 0)
{
v___y_1027_ = v___x_1057_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
if (v___x_1059_ == 0)
{
if (v___x_1058_ == 0)
{
v___y_1027_ = v___x_1057_;
goto v___jp_1026_;
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1056_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_970_, v_imports_1004_, v___x_1060_, v___x_1061_, v___x_1057_);
v___y_1027_ = v___x_1062_;
goto v___jp_1026_;
}
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1056_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_970_, v_imports_1004_, v___x_1063_, v___x_1064_, v___x_1057_);
v___y_1027_ = v___x_1065_;
goto v___jp_1026_;
}
}
v___jp_1006_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1);
v___x_1008_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1005_);
v___x_1009_ = l_Lean_MessageData_ofName(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_snd_987_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_fst_986_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_array_push(v_b_974_, v___x_1014_);
v_a_979_ = v___x_1015_;
goto v___jp_978_;
}
v___jp_1016_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc(v_check_1005_);
v___x_1020_ = lean_apply_1(v_val_1017_, v_check_1005_);
v___x_1021_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_snd_987_, v___x_1020_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_dec_ref_known(v___x_1021_, 1);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_979_ = v_b_974_;
goto v___jp_978_;
}
else
{
lean_object* v_a_1022_; uint8_t v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_Exception_isInterrupt(v_a_1022_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; 
lean_inc(v_a_1022_);
v___x_1024_ = l_Lean_Exception_isRuntime(v_a_1022_);
v___y_992_ = v_a_1022_;
v___y_993_ = v___x_1024_;
goto v___jp_991_;
}
else
{
v___y_992_ = v_a_1022_;
v___y_993_ = v___x_1023_;
goto v___jp_991_;
}
}
}
v___jp_1026_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v___y_1027_);
v___x_1029_ = lean_nat_dec_eq(v___x_1028_, v___x_1025_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_del_object(v___x_989_);
v___x_1030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5);
v___x_1031_ = lean_array_to_list(v___y_1027_);
v___x_1032_ = lean_box(0);
v___x_1033_ = l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Lean_MessageData_ofList(v___x_1033_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_snd_987_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_fst_986_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_array_push(v_b_974_, v___x_1039_);
v_a_979_ = v___x_1040_;
goto v___jp_978_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec_ref(v___y_1027_);
v___x_1041_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1005_);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_968_, v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 1)
{
lean_dec(v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_del_object(v___x_989_);
goto v___jp_1006_;
}
else
{
lean_object* v_val_1043_; 
v_val_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_val_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_val_1017_ = v_val_1043_;
v___y_1018_ = v___y_975_;
v___y_1019_ = v___y_976_;
goto v___jp_1016_;
}
}
else
{
lean_object* v___x_1044_; 
lean_dec(v___x_1042_);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_969_, v___x_1041_);
lean_dec(v___x_1041_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_val_1045_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_val_1017_ = v_a_1047_;
v___y_1018_ = v___y_975_;
v___y_1019_ = v___y_976_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec_ref(v_b_974_);
lean_dec_ref(v_shouldCheck_967_);
v_a_1048_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1046_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_dec(v___x_1044_);
lean_del_object(v___x_989_);
goto v___jp_1006_;
}
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec_ref(v_b_974_);
lean_dec_ref(v_shouldCheck_967_);
v_a_1066_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1001_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1001_);
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
v___jp_991_:
{
if (v___y_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_Lean_Exception_toMessageData(v___y_992_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_994_);
lean_ctor_set(v___x_989_, 0, v_snd_987_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_snd_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_999_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_fst_986_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_array_push(v_b_974_, v___x_997_);
v_a_979_ = v___x_998_;
goto v___jp_978_;
}
}
else
{
lean_object* v___x_1000_; 
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec_ref(v_b_974_);
lean_dec_ref(v_shouldCheck_967_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___y_992_);
return v___x_1000_;
}
}
}
}
v___jp_978_:
{
size_t v___x_980_; size_t v___x_981_; 
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_973_, v___x_980_);
v_i_973_ = v___x_981_;
v_b_974_ = v_a_979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___boxed(lean_object* v_shouldCheck_1075_, lean_object* v_val_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v_as_1079_, lean_object* v_sz_1080_, lean_object* v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1080_);
lean_dec(v_sz_1080_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1081_);
lean_dec(v_i_1081_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1075_, v_val_1076_, v___x_1077_, v___y_1078_, v_as_1079_, v_sz_boxed_1086_, v_i_boxed_1087_, v_b_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_as_1079_);
lean_dec(v___y_1078_);
lean_dec(v___x_1077_);
lean_dec(v_val_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run(lean_object* v_inPackage_1091_, lean_object* v_shouldCheck_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v___x_1100_; lean_object* v_toEnvExtension_1101_; lean_object* v_asyncMode_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___y_1111_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1096_ = lean_st_ref_get(v_a_1094_);
v___x_1097_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_1098_ = lean_st_ref_get(v___x_1097_);
v_env_1099_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref_n(v_env_1099_, 2);
lean_dec(v___x_1096_);
v___x_1100_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_1101_ = lean_ctor_get(v___x_1100_, 0);
v_asyncMode_1102_ = lean_ctor_get(v_toEnvExtension_1101_, 2);
v___x_1103_ = lean_box(1);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1103_, v___x_1100_, v_env_1099_, v_asyncMode_1102_, v___x_1104_);
v___x_1106_ = l_Lean_NameSet_empty;
v___x_1107_ = l_Lean_Environment_header(v_env_1099_);
v___x_1108_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1107_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_array_get_size(v___x_1108_);
v___x_1118_ = lean_nat_dec_lt(v___x_1109_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec_ref(v___x_1108_);
v___y_1111_ = v___x_1106_;
goto v___jp_1110_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_nat_dec_le(v___x_1117_, v___x_1117_);
if (v___x_1119_ == 0)
{
if (v___x_1118_ == 0)
{
lean_dec_ref(v___x_1108_);
v___y_1111_ = v___x_1106_;
goto v___jp_1110_;
}
else
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1117_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v___x_1108_, v___x_1120_, v___x_1121_, v___x_1106_);
lean_dec_ref(v___x_1108_);
v___y_1111_ = v___x_1122_;
goto v___jp_1110_;
}
}
else
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = lean_usize_of_nat(v___x_1117_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v___x_1108_, v___x_1123_, v___x_1124_, v___x_1106_);
lean_dec_ref(v___x_1108_);
v___y_1111_ = v___x_1125_;
goto v___jp_1110_;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = ((lean_object*)(l_Lean_Doc_DeferredCheck_run___closed__0));
v___x_1113_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(v_env_1099_, v_inPackage_1091_);
v_sz_1114_ = lean_array_size(v___x_1113_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1092_, v___x_1098_, v___x_1105_, v___y_1111_, v___x_1113_, v_sz_1114_, v___x_1115_, v___x_1112_, v_a_1093_, v_a_1094_);
lean_dec_ref(v___x_1113_);
lean_dec(v___y_1111_);
lean_dec(v___x_1105_);
lean_dec(v___x_1098_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run___boxed(lean_object* v_inPackage_1126_, lean_object* v_shouldCheck_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Doc_DeferredCheck_run(v_inPackage_1126_, v_shouldCheck_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
return v_res_1131_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
