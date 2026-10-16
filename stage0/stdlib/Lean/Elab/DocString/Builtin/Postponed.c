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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_Context_setOptions(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "invalid `deferred_doc_check` syntax"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `deferred_doc_check`, must be global"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__32_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__33_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__31_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__value)} };
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
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__value)} };
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "the check requires "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " to be imported, but they are not"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "no handler registered for deferred check `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
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
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_130_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v___x_128_, v___x_132_, v___x_133_, v_b_121_);
v___y_123_ = v___x_134_;
goto v___jp_122_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_135_, lean_object* v_i_136_, lean_object* v_stop_137_, lean_object* v_b_138_){
_start:
{
size_t v_i_boxed_139_; size_t v_stop_boxed_140_; lean_object* v_res_141_; 
v_i_boxed_139_ = lean_unbox_usize(v_i_136_);
lean_dec(v_i_136_);
v_stop_boxed_140_ = lean_unbox_usize(v_stop_137_);
lean_dec(v_stop_137_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_as_135_, v_i_boxed_139_, v_stop_boxed_140_, v_b_138_);
lean_dec_ref(v_as_135_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_nss_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_143_ = lean_box(1);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_get_size(v_nss_142_);
v___x_146_ = lean_nat_dec_lt(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
return v___x_143_;
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_145_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_nss_142_, v___x_147_, v___x_148_, v___x_143_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_nss_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(v_nss_150_);
lean_dec_ref(v_nss_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_es_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_array_mk(v_es_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_));
v___x_174_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(1);
v___x_179_ = lean_st_mk_ref(v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler(lean_object* v_key_183_, lean_object* v_impl_184_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_186_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_187_ = lean_st_ref_take(v___x_186_);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_key_183_, v_impl_184_, v___x_187_);
v___x_189_ = lean_st_ref_put(v___x_186_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler___boxed(lean_object* v_key_191_, lean_object* v_impl_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Doc_DeferredCheck_addBuiltinHandler(v_key_191_, v_impl_192_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_199_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v___x_200_);
lean_ctor_set(v___x_201_, 4, v___x_199_);
lean_ctor_set(v___x_201_, 5, v___x_199_);
lean_ctor_set(v___x_201_, 6, v___x_199_);
lean_ctor_set(v___x_201_, 7, v___x_199_);
lean_ctor_set(v___x_201_, 8, v___x_199_);
lean_ctor_set(v___x_201_, 9, v___x_199_);
lean_ctor_set(v___x_201_, 10, v___x_199_);
lean_ctor_set(v___x_201_, 11, v___x_198_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_205_ = ((size_t)5ULL);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_unsigned_to_nat(32u);
v___x_208_ = lean_mk_empty_array_with_capacity(v___x_207_);
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_206_);
lean_ctor_set(v___x_210_, 3, v___x_206_);
lean_ctor_set_usize(v___x_210_, 4, v___x_205_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(1);
v___x_212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_211_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_toCold_220_; lean_object* v_env_221_; lean_object* v_options_222_; uint8_t v___x_223_; lean_object* v_env_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_219_ = lean_st_ref_get(v___y_217_);
v_toCold_220_ = lean_ctor_get(v___y_216_, 0);
v_env_221_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_env_221_);
lean_dec(v___x_219_);
v_options_222_ = lean_ctor_get(v_toCold_220_, 2);
v___x_223_ = 0;
v_env_224_ = l_Lean_Environment_setRecordingDeps(v_env_221_, v___x_223_);
v___x_225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_222_);
v___x_227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_227_, 0, v_env_224_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_ctor_set(v___x_227_, 3, v_options_222_);
v___x_228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_msgData_215_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_ref_239_; lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_ref_239_ = lean_ctor_get(v___y_236_, 2);
v___x_240_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_235_, v___y_236_, v___y_237_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_inc(v_ref_239_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_ref_239_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_259_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v_x_255_, 1);
v___x_260_ = l_Lean_stringToMessageData(v_a_259_);
v___x_261_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_260_, v___y_256_, v___y_257_);
return v___x_261_;
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v_x_255_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v_x_255_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v_x_255_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 0);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_274_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_box(0);
v___x_276_ = l_Lean_Elab_abortCommandExceptionId;
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(lean_object* v_typeName_283_, lean_object* v_constName_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; uint8_t v___x_290_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
lean_inc(v_constName_284_);
v___x_290_ = lean_has_compile_error(v_env_289_, v_constName_284_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v_env_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_291_ = lean_st_ref_get(v___y_286_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
lean_dec(v___x_291_);
v___x_293_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_285_);
v___x_294_ = l_Lean_Environment_evalConstCheck___redArg(v_env_292_, v___x_293_, v_typeName_283_, v_constName_284_);
lean_dec_ref(v___x_293_);
v___x_295_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_294_, v___y_285_, v___y_286_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; lean_object* v_env_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref_known(v___x_296_, 1);
v___x_297_ = lean_st_ref_get(v___y_286_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_297_);
v___x_299_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_285_);
v___x_300_ = l_Lean_Environment_evalConstCheck___redArg(v_env_298_, v___x_299_, v_typeName_283_, v_constName_284_);
lean_dec_ref(v___x_299_);
v___x_301_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_300_, v___y_285_, v___y_286_);
return v___x_301_;
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_constName_284_);
lean_dec(v_typeName_283_);
v_a_302_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_296_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_296_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_310_, lean_object* v_constName_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_310_, v_constName_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(lean_object* v_declName_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1));
v___x_326_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v___x_325_, v_declName_321_, v_a_322_, v_a_323_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___boxed(lean_object* v_declName_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_declName_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_object* v_00_u03b1_342_, lean_object* v_typeName_343_, lean_object* v_constName_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_343_, v_constName_344_, v___y_345_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_349_, lean_object* v_typeName_350_, lean_object* v_constName_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(v_00_u03b1_349_, v_typeName_350_, v_constName_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_356_, lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_357_, v___y_358_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_362_, v_x_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_374_, v_msg_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v_addEntryFn_380_, lean_object* v___x_381_, lean_object* v_s_382_){
_start:
{
lean_object* v_importedEntries_383_; lean_object* v_state_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_importedEntries_383_ = lean_ctor_get(v_s_382_, 0);
v_state_384_ = lean_ctor_get(v_s_382_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_s_382_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v_s_382_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_state_384_);
lean_inc(v_importedEntries_383_);
lean_dec(v_s_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_state_388_; lean_object* v___x_390_; 
v_state_388_ = lean_apply_2(v_addEntryFn_380_, v_state_384_, v___x_381_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_state_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_importedEntries_383_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_state_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v_decl_410_, lean_object* v_stx_411_, uint8_t v_kind_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___y_417_; lean_object* v_nextMacroScope_418_; lean_object* v_ngen_419_; lean_object* v_auxDeclNGen_420_; lean_object* v_traceState_421_; lean_object* v_recordedDeps_422_; lean_object* v_messages_423_; lean_object* v_infoState_424_; lean_object* v_snapshotTasks_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v_key_433_; lean_object* v___y_434_; uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = 0;
v___x_510_ = l_Lean_instBEqAttributeKind_beq(v_kind_412_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_stx_411_);
lean_dec(v_decl_410_);
lean_dec_ref(v___x_407_);
lean_dec(v___x_406_);
v___x_511_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_512_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_511_, v___y_413_, v___y_414_);
return v___x_512_;
}
else
{
goto v___jp_457_;
}
v___jp_416_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_429_, 0, v___y_427_);
lean_ctor_set(v___x_429_, 1, v_nextMacroScope_418_);
lean_ctor_set(v___x_429_, 2, v_ngen_419_);
lean_ctor_set(v___x_429_, 3, v_auxDeclNGen_420_);
lean_ctor_set(v___x_429_, 4, v_traceState_421_);
lean_ctor_set(v___x_429_, 5, v___x_428_);
lean_ctor_set(v___x_429_, 6, v_recordedDeps_422_);
lean_ctor_set(v___x_429_, 7, v_messages_423_);
lean_ctor_set(v___x_429_, 8, v_infoState_424_);
lean_ctor_set(v___x_429_, 9, v_snapshotTasks_425_);
v___x_430_ = lean_st_ref_put(v___y_417_, v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___y_426_);
return v___x_431_;
}
v___jp_432_:
{
lean_object* v___x_435_; lean_object* v_env_436_; lean_object* v_nextMacroScope_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_traceState_440_; lean_object* v_recordedDeps_441_; lean_object* v_messages_442_; lean_object* v_infoState_443_; lean_object* v_snapshotTasks_444_; lean_object* v___x_445_; lean_object* v_toEnvExtension_446_; lean_object* v_addEntryFn_447_; lean_object* v_asyncMode_448_; uint8_t v_logWrites_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___f_452_; uint8_t v___x_453_; 
v___x_435_ = lean_st_ref_take(v___y_434_);
v_env_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_env_436_);
v_nextMacroScope_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_nextMacroScope_437_);
v_ngen_438_ = lean_ctor_get(v___x_435_, 2);
lean_inc_ref(v_ngen_438_);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_435_, 3);
lean_inc_ref(v_auxDeclNGen_439_);
v_traceState_440_ = lean_ctor_get(v___x_435_, 4);
lean_inc_ref(v_traceState_440_);
v_recordedDeps_441_ = lean_ctor_get(v___x_435_, 6);
lean_inc_ref(v_recordedDeps_441_);
v_messages_442_ = lean_ctor_get(v___x_435_, 7);
lean_inc_ref(v_messages_442_);
v_infoState_443_ = lean_ctor_get(v___x_435_, 8);
lean_inc_ref(v_infoState_443_);
v_snapshotTasks_444_ = lean_ctor_get(v___x_435_, 9);
lean_inc_ref(v_snapshotTasks_444_);
lean_dec(v___x_435_);
v___x_445_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_446_ = lean_ctor_get(v___x_445_, 0);
v_addEntryFn_447_ = lean_ctor_get(v___x_445_, 3);
v_asyncMode_448_ = lean_ctor_get(v_toEnvExtension_446_, 2);
v_logWrites_449_ = lean_ctor_get_uint8(v_toEnvExtension_446_, sizeof(void*)*6);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_key_433_);
lean_ctor_set(v___x_451_, 1, v_decl_410_);
lean_inc(v_addEntryFn_447_);
v___f_452_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_452_, 0, v_addEntryFn_447_);
lean_closure_set(v___f_452_, 1, v___x_451_);
v___x_453_ = 1;
if (v_logWrites_449_ == 0)
{
lean_object* v___x_454_; 
lean_inc_ref(v_toEnvExtension_446_);
v___x_454_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_446_, v_env_436_, v___f_452_, v_asyncMode_448_, v___x_406_, v___x_453_);
v___y_417_ = v___y_434_;
v_nextMacroScope_418_ = v_nextMacroScope_437_;
v_ngen_419_ = v_ngen_438_;
v_auxDeclNGen_420_ = v_auxDeclNGen_439_;
v_traceState_421_ = v_traceState_440_;
v_recordedDeps_422_ = v_recordedDeps_441_;
v_messages_423_ = v_messages_442_;
v_infoState_424_ = v_infoState_443_;
v_snapshotTasks_425_ = v_snapshotTasks_444_;
v___y_426_ = v___x_450_;
v___y_427_ = v___x_454_;
goto v___jp_416_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc_ref_n(v_toEnvExtension_446_, 2);
v___x_455_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_446_, v_env_436_);
lean_dec_ref(v_env_436_);
v___x_456_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_446_, v___x_455_, v___f_452_, v_asyncMode_448_, v___x_406_, v___x_453_);
v___y_417_ = v___y_434_;
v_nextMacroScope_418_ = v_nextMacroScope_437_;
v_ngen_419_ = v_ngen_438_;
v_auxDeclNGen_420_ = v_auxDeclNGen_439_;
v_traceState_421_ = v_traceState_440_;
v_recordedDeps_422_ = v_recordedDeps_441_;
v_messages_423_ = v_messages_442_;
v_infoState_424_ = v_infoState_443_;
v_snapshotTasks_425_ = v_snapshotTasks_444_;
v___y_426_ = v___x_450_;
v___y_427_ = v___x_456_;
goto v___jp_416_;
}
}
v___jp_457_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_461_ = l_Lean_Name_mkStr4(v___x_407_, v___x_458_, v___x_459_, v___x_460_);
lean_inc(v_stx_411_);
v___x_462_ = l_Lean_Syntax_isOfKind(v_stx_411_, v___x_461_);
lean_dec(v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_stx_411_);
lean_dec(v_decl_410_);
lean_dec(v___x_406_);
v___x_463_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_464_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_463_, v___y_413_, v___y_414_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = l_Lean_Syntax_getArg(v_stx_411_, v___x_408_);
v___x_474_ = l_Lean_Syntax_matchesIdent(v___x_473_, v___x_409_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_stx_411_);
lean_dec(v_decl_410_);
lean_dec(v___x_406_);
v___x_475_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_476_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_475_, v___y_413_, v___y_414_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = l_Lean_Syntax_getArg(v_stx_411_, v___x_485_);
lean_dec(v_stx_411_);
lean_inc(v___x_486_);
v___x_487_ = l_Lean_Syntax_matchesNull(v___x_486_, v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___x_486_);
lean_dec(v_decl_410_);
lean_dec(v___x_406_);
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_489_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_488_, v___y_413_, v___y_414_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = l_Lean_Syntax_getArg(v___x_486_, v___x_408_);
lean_dec(v___x_486_);
v___x_499_ = l_Lean_realizeGlobalConstNoOverload(v___x_498_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v_key_433_ = v_a_500_;
v___y_434_ = v___y_414_;
goto v___jp_432_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_decl_410_);
lean_dec(v___x_406_);
v_a_501_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_499_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v_decl_517_, lean_object* v_stx_518_, lean_object* v_kind_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_kind_boxed_523_; lean_object* v_res_524_; 
v_kind_boxed_523_ = lean_unbox(v_kind_519_);
v_res_524_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_513_, v___x_514_, v___x_515_, v___x_516_, v_decl_517_, v_stx_518_, v_kind_boxed_523_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___x_516_);
lean_dec(v___x_515_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_531_, lean_object* v_decl_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_536_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_537_ = l_Lean_MessageData_ofName(v___x_531_);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_540_, v___y_533_, v___y_534_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_542_, lean_object* v_decl_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_542_, v_decl_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v_decl_543_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_642_ = l_Lean_registerBuiltinAttribute(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v_decl_657_, lean_object* v_stx_658_, uint8_t v_kind_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_key_664_; lean_object* v___y_665_; lean_object* v___y_666_; uint8_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 0;
v___x_728_ = l_Lean_instBEqAttributeKind_beq(v_kind_659_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_stx_658_);
lean_dec(v_decl_657_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
v___x_729_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_730_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_729_, v___y_660_, v___y_661_);
return v___x_730_;
}
else
{
goto v___jp_675_;
}
v___jp_663_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_668_ = l_Lean_Name_mkStr4(v___x_652_, v___x_653_, v___x_654_, v___x_667_);
v___x_669_ = lean_box(0);
v___x_670_ = l_Lean_Expr_const___override(v___x_668_, v___x_669_);
v___x_671_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_key_664_);
lean_inc(v_decl_657_);
v___x_672_ = l_Lean_Expr_const___override(v_decl_657_, v___x_669_);
v___x_673_ = l_Lean_mkAppB(v___x_670_, v___x_671_, v___x_672_);
v___x_674_ = l_Lean_declareBuiltin(v_decl_657_, v___x_673_, v___y_665_, v___y_666_);
return v___x_674_;
}
v___jp_675_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
lean_inc_ref(v___x_652_);
v___x_679_ = l_Lean_Name_mkStr4(v___x_652_, v___x_676_, v___x_677_, v___x_678_);
lean_inc(v_stx_658_);
v___x_680_ = l_Lean_Syntax_isOfKind(v_stx_658_, v___x_679_);
lean_dec(v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_stx_658_);
lean_dec(v_decl_657_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
v___x_681_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_682_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_681_, v___y_660_, v___y_661_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = l_Lean_Syntax_getArg(v_stx_658_, v___x_655_);
v___x_692_ = l_Lean_Syntax_matchesIdent(v___x_691_, v___x_656_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_stx_658_);
lean_dec(v_decl_657_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
v___x_693_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_694_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_693_, v___y_660_, v___y_661_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = l_Lean_Syntax_getArg(v_stx_658_, v___x_703_);
lean_dec(v_stx_658_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_Syntax_matchesNull(v___x_704_, v___x_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v___x_704_);
lean_dec(v_decl_657_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
v___x_706_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_707_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_706_, v___y_660_, v___y_661_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = l_Lean_Syntax_getArg(v___x_704_, v___x_655_);
lean_dec(v___x_704_);
v___x_717_ = l_Lean_realizeGlobalConstNoOverload(v___x_716_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v_key_664_ = v_a_718_;
v___y_665_ = v___y_660_;
v___y_666_ = v___y_661_;
goto v___jp_663_;
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_decl_657_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
v_a_719_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v_decl_736_, lean_object* v_stx_737_, lean_object* v_kind_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v_kind_boxed_742_; lean_object* v_res_743_; 
v_kind_boxed_742_ = lean_unbox(v_kind_738_);
v_res_743_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(v___x_731_, v___x_732_, v___x_733_, v___x_734_, v___x_735_, v_decl_736_, v_stx_737_, v_kind_boxed_742_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___x_735_);
lean_dec(v___x_734_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_779_ = l_Lean_registerBuiltinAttribute(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(lean_object* v_c_782_, lean_object* v_act_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_currNamespace_787_; lean_object* v_openDecls_788_; lean_object* v_options_789_; lean_object* v___x_790_; lean_object* v_toCold_791_; lean_object* v_currRecDepth_792_; lean_object* v_ref_793_; uint16_t v_optionFlags_794_; uint8_t v_suppressElabErrors_795_; uint8_t v_isRecordingDeps_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_823_; 
v_currNamespace_787_ = lean_ctor_get(v_c_782_, 4);
lean_inc(v_currNamespace_787_);
v_openDecls_788_ = lean_ctor_get(v_c_782_, 5);
lean_inc(v_openDecls_788_);
v_options_789_ = lean_ctor_get(v_c_782_, 6);
lean_inc_ref(v_options_789_);
lean_dec_ref(v_c_782_);
lean_inc_ref(v_a_784_);
v___x_790_ = l_Lean_Core_Context_setOptions(v_a_784_, v_options_789_);
v_toCold_791_ = lean_ctor_get(v___x_790_, 0);
v_currRecDepth_792_ = lean_ctor_get(v___x_790_, 1);
v_ref_793_ = lean_ctor_get(v___x_790_, 2);
v_optionFlags_794_ = lean_ctor_get_uint16(v___x_790_, sizeof(void*)*3);
v_suppressElabErrors_795_ = lean_ctor_get_uint8(v___x_790_, sizeof(void*)*3 + 2);
v_isRecordingDeps_796_ = lean_ctor_get_uint8(v___x_790_, sizeof(void*)*3 + 3);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_823_ == 0)
{
v___x_798_ = v___x_790_;
v_isShared_799_ = v_isSharedCheck_823_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_ref_793_);
lean_inc(v_currRecDepth_792_);
lean_inc(v_toCold_791_);
lean_dec(v___x_790_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_823_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fileName_800_; lean_object* v_fileMap_801_; lean_object* v_options_802_; lean_object* v_maxRecDepth_803_; lean_object* v_initHeartbeats_804_; lean_object* v_maxHeartbeats_805_; lean_object* v_quotContext_806_; lean_object* v_currMacroScope_807_; lean_object* v_cancelTk_x3f_808_; lean_object* v_inheritedTraceOptions_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_820_; 
v_fileName_800_ = lean_ctor_get(v_toCold_791_, 0);
v_fileMap_801_ = lean_ctor_get(v_toCold_791_, 1);
v_options_802_ = lean_ctor_get(v_toCold_791_, 2);
v_maxRecDepth_803_ = lean_ctor_get(v_toCold_791_, 3);
v_initHeartbeats_804_ = lean_ctor_get(v_toCold_791_, 6);
v_maxHeartbeats_805_ = lean_ctor_get(v_toCold_791_, 7);
v_quotContext_806_ = lean_ctor_get(v_toCold_791_, 8);
v_currMacroScope_807_ = lean_ctor_get(v_toCold_791_, 9);
v_cancelTk_x3f_808_ = lean_ctor_get(v_toCold_791_, 10);
v_inheritedTraceOptions_809_ = lean_ctor_get(v_toCold_791_, 11);
v_isSharedCheck_820_ = !lean_is_exclusive(v_toCold_791_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_821_ = lean_ctor_get(v_toCold_791_, 5);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_toCold_791_, 4);
lean_dec(v_unused_822_);
v___x_811_ = v_toCold_791_;
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_inheritedTraceOptions_809_);
lean_inc(v_cancelTk_x3f_808_);
lean_inc(v_currMacroScope_807_);
lean_inc(v_quotContext_806_);
lean_inc(v_maxHeartbeats_805_);
lean_inc(v_initHeartbeats_804_);
lean_inc(v_maxRecDepth_803_);
lean_inc(v_options_802_);
lean_inc(v_fileMap_801_);
lean_inc(v_fileName_800_);
lean_dec(v_toCold_791_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v_openDecls_788_);
lean_ctor_set(v___x_811_, 4, v_currNamespace_787_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fileName_800_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_fileMap_801_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_options_802_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_maxRecDepth_803_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_currNamespace_787_);
lean_ctor_set(v_reuseFailAlloc_819_, 5, v_openDecls_788_);
lean_ctor_set(v_reuseFailAlloc_819_, 6, v_initHeartbeats_804_);
lean_ctor_set(v_reuseFailAlloc_819_, 7, v_maxHeartbeats_805_);
lean_ctor_set(v_reuseFailAlloc_819_, 8, v_quotContext_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 9, v_currMacroScope_807_);
lean_ctor_set(v_reuseFailAlloc_819_, 10, v_cancelTk_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_819_, 11, v_inheritedTraceOptions_809_);
v___x_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_814_);
v___x_816_ = v___x_798_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_currRecDepth_792_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_ref_793_);
lean_ctor_set_uint16(v_reuseFailAlloc_818_, sizeof(void*)*3, v_optionFlags_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*3 + 2, v_suppressElabErrors_795_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*3 + 3, v_isRecordingDeps_796_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
lean_inc(v_a_785_);
v___x_817_ = lean_apply_3(v_act_783_, v___x_816_, v_a_785_, lean_box(0));
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg___boxed(lean_object* v_c_824_, lean_object* v_act_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_824_, v_act_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_object* v_00_u03b1_830_, lean_object* v_c_831_, lean_object* v_act_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_831_, v_act_832_, v_a_833_, v_a_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___boxed(lean_object* v_00_u03b1_837_, lean_object* v_c_838_, lean_object* v_act_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(v_00_u03b1_837_, v_c_838_, v_act_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(lean_object* v___x_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_bs_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_848_ == 0)
{
lean_dec(v___x_844_);
return v_bs_847_;
}
else
{
lean_object* v_v_849_; lean_object* v___x_850_; lean_object* v_bs_x27_851_; lean_object* v___x_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
v_v_849_ = lean_array_uget(v_bs_847_, v_i_846_);
v___x_850_ = lean_unsigned_to_nat(0u);
v_bs_x27_851_ = lean_array_uset(v_bs_847_, v_i_846_, v___x_850_);
lean_inc(v___x_844_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_844_);
lean_ctor_set(v___x_852_, 1, v_v_849_);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_add(v_i_846_, v___x_853_);
v___x_855_ = lean_array_uset(v_bs_x27_851_, v_i_846_, v___x_852_);
v_i_846_ = v___x_854_;
v_bs_847_ = v___x_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0___boxed(lean_object* v___x_857_, lean_object* v_sz_858_, lean_object* v_i_859_, lean_object* v_bs_860_){
_start:
{
size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v_sz_boxed_861_ = lean_unbox_usize(v_sz_858_);
lean_dec(v_sz_858_);
v_i_boxed_862_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_857_, v_sz_boxed_861_, v_i_boxed_862_, v_bs_860_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Array_instInhabited___redArg();
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(lean_object* v___x_865_, lean_object* v_inPackage_866_, lean_object* v_env_867_, lean_object* v_range_868_, lean_object* v_b_869_, lean_object* v_i_870_){
_start:
{
lean_object* v_stop_871_; lean_object* v_step_872_; lean_object* v_a_874_; uint8_t v___x_877_; 
v_stop_871_ = lean_ctor_get(v_range_868_, 1);
v_step_872_ = lean_ctor_get(v_range_868_, 2);
v___x_877_ = lean_nat_dec_lt(v_i_870_, v_stop_871_);
if (v___x_877_ == 0)
{
lean_dec(v_i_870_);
lean_dec_ref(v_inPackage_866_);
return v_b_869_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_878_ = lean_box(0);
v___x_879_ = lean_array_get_borrowed(v___x_878_, v___x_865_, v_i_870_);
lean_inc_ref(v_inPackage_866_);
lean_inc(v___x_879_);
v___x_880_ = lean_apply_1(v_inPackage_866_, v___x_879_);
v___x_881_ = lean_unbox(v___x_880_);
if (v___x_881_ == 0)
{
v_a_874_ = v_b_869_;
goto v___jp_873_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_882_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_883_ = l_Lean_Doc_deferredCheckExt;
v___x_884_ = 0;
v___x_885_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_882_, v___x_883_, v_env_867_, v_i_870_, v___x_884_);
v_sz_886_ = lean_array_size(v___x_885_);
v___x_887_ = ((size_t)0ULL);
lean_inc(v___x_879_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_879_, v_sz_886_, v___x_887_, v___x_885_);
v___x_889_ = l_Array_append___redArg(v_b_869_, v___x_888_);
lean_dec_ref(v___x_888_);
v_a_874_ = v___x_889_;
goto v___jp_873_;
}
}
v___jp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = lean_nat_add(v_i_870_, v_step_872_);
lean_dec(v_i_870_);
v_b_869_ = v_a_874_;
v_i_870_ = v___x_875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___boxed(lean_object* v___x_890_, lean_object* v_inPackage_891_, lean_object* v_env_892_, lean_object* v_range_893_, lean_object* v_b_894_, lean_object* v_i_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_890_, v_inPackage_891_, v_env_892_, v_range_893_, v_b_894_, v_i_895_);
lean_dec_ref(v_range_893_);
lean_dec_ref(v_env_892_);
lean_dec_ref(v___x_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(lean_object* v_env_899_, lean_object* v_inPackage_900_){
_start:
{
lean_object* v___x_901_; lean_object* v_moduleNames_902_; lean_object* v___x_903_; lean_object* v_out_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_901_ = l_Lean_Environment_header(v_env_899_);
v_moduleNames_902_ = lean_ctor_get(v___x_901_, 4);
lean_inc_ref(v_moduleNames_902_);
lean_dec_ref(v___x_901_);
v___x_903_ = lean_unsigned_to_nat(0u);
v_out_904_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0));
v___x_905_ = lean_array_get_size(v_moduleNames_902_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v___x_903_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_inc_ref(v_inPackage_900_);
v___x_908_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v_moduleNames_902_, v_inPackage_900_, v_env_899_, v___x_907_, v_out_904_, v___x_903_);
lean_dec_ref_known(v___x_907_, 3);
lean_dec_ref(v_moduleNames_902_);
v___x_909_ = l_Lean_Environment_mainModule(v_env_899_);
lean_inc(v___x_909_);
v___x_910_ = lean_apply_1(v_inPackage_900_, v___x_909_);
v___x_911_ = lean_unbox(v___x_910_);
if (v___x_911_ == 0)
{
lean_dec(v___x_909_);
lean_dec_ref(v_env_899_);
return v___x_908_;
}
else
{
lean_object* v___x_912_; lean_object* v_toEnvExtension_913_; lean_object* v_asyncMode_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; size_t v_sz_919_; size_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_912_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_913_ = lean_ctor_get(v___x_912_, 0);
v_asyncMode_914_ = lean_ctor_get(v_toEnvExtension_913_, 2);
v___x_915_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_916_ = lean_box(0);
v___x_917_ = 0;
v___x_918_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_915_, v___x_912_, v_env_899_, v_asyncMode_914_, v___x_916_, v___x_917_);
v_sz_919_ = lean_array_size(v___x_918_);
v___x_920_ = ((size_t)0ULL);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_909_, v_sz_919_, v___x_920_, v___x_918_);
v___x_922_ = l_Array_append___redArg(v___x_908_, v___x_921_);
lean_dec_ref(v___x_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(lean_object* v___x_923_, lean_object* v_inPackage_924_, lean_object* v_env_925_, lean_object* v_range_926_, lean_object* v_b_927_, lean_object* v_i_928_, lean_object* v_hs_929_, lean_object* v_hl_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_923_, v_inPackage_924_, v_env_925_, v_range_926_, v_b_927_, v_i_928_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___boxed(lean_object* v___x_932_, lean_object* v_inPackage_933_, lean_object* v_env_934_, lean_object* v_range_935_, lean_object* v_b_936_, lean_object* v_i_937_, lean_object* v_hs_938_, lean_object* v_hl_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(v___x_932_, v_inPackage_933_, v_env_934_, v_range_935_, v_b_936_, v_i_937_, v_hs_938_, v_hl_939_);
lean_dec_ref(v_range_935_);
lean_dec_ref(v_env_934_);
lean_dec_ref(v___x_932_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(lean_object* v_as_941_, size_t v_i_942_, size_t v_stop_943_, lean_object* v_b_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_eq(v_i_942_, v_stop_943_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; size_t v___x_948_; size_t v___x_949_; 
v___x_946_ = lean_array_uget_borrowed(v_as_941_, v_i_942_);
lean_inc(v___x_946_);
v___x_947_ = l_Lean_NameSet_insert(v_b_944_, v___x_946_);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_add(v_i_942_, v___x_948_);
v_i_942_ = v___x_949_;
v_b_944_ = v___x_947_;
goto _start;
}
else
{
return v_b_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3___boxed(lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_stop_953_, lean_object* v_b_954_){
_start:
{
size_t v_i_boxed_955_; size_t v_stop_boxed_956_; lean_object* v_res_957_; 
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_956_ = lean_unbox_usize(v_stop_953_);
lean_dec(v_stop_953_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_as_951_, v_i_boxed_955_, v_stop_boxed_956_, v_b_954_);
lean_dec_ref(v_as_951_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(lean_object* v___y_958_, lean_object* v_as_959_, size_t v_i_960_, size_t v_stop_961_, lean_object* v_b_962_){
_start:
{
lean_object* v___y_964_; uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_eq(v_i_960_, v_stop_961_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_array_uget_borrowed(v_as_959_, v_i_960_);
v___x_970_ = l_Lean_NameSet_contains(v___y_958_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_inc(v___x_969_);
v___x_971_ = lean_array_push(v_b_962_, v___x_969_);
v___y_964_ = v___x_971_;
goto v___jp_963_;
}
else
{
v___y_964_ = v_b_962_;
goto v___jp_963_;
}
}
else
{
return v_b_962_;
}
v___jp_963_:
{
size_t v___x_965_; size_t v___x_966_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_960_, v___x_965_);
v_i_960_ = v___x_966_;
v_b_962_ = v___y_964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1___boxed(lean_object* v___y_972_, lean_object* v_as_973_, lean_object* v_i_974_, lean_object* v_stop_975_, lean_object* v_b_976_){
_start:
{
size_t v_i_boxed_977_; size_t v_stop_boxed_978_; lean_object* v_res_979_; 
v_i_boxed_977_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_stop_boxed_978_ = lean_unbox_usize(v_stop_975_);
lean_dec(v_stop_975_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_972_, v_as_973_, v_i_boxed_977_, v_stop_boxed_978_, v_b_976_);
lean_dec_ref(v_as_973_);
lean_dec(v___y_972_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
if (lean_obj_tag(v_a_980_) == 0)
{
lean_object* v___x_982_; 
v___x_982_ = l_List_reverse___redArg(v_a_981_);
return v___x_982_;
}
else
{
lean_object* v_head_983_; lean_object* v_tail_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
v_head_983_ = lean_ctor_get(v_a_980_, 0);
v_tail_984_ = lean_ctor_get(v_a_980_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_980_);
if (v_isSharedCheck_993_ == 0)
{
v___x_986_ = v_a_980_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_tail_984_);
lean_inc(v_head_983_);
lean_dec(v_a_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = l_Lean_MessageData_ofName(v_head_983_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_a_981_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_a_981_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v_a_980_ = v_tail_984_;
v_a_981_ = v___x_990_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(lean_object* v_shouldCheck_1008_, lean_object* v_val_1009_, lean_object* v___x_1010_, lean_object* v___y_1011_, lean_object* v_as_1012_, size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_a_1020_; uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v_shouldCheck_1008_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_b_1015_);
return v___x_1025_;
}
else
{
lean_object* v_a_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1116_; 
v_a_1026_ = lean_array_uget(v_as_1012_, v_i_1014_);
v_fst_1027_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1030_ = v_a_1026_;
v_isShared_1031_ = v_isSharedCheck_1116_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1116_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_val_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_shouldCheck_1008_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v_snd_1028_);
v___x_1059_ = lean_apply_4(v_shouldCheck_1008_, v_snd_1028_, v___y_1016_, v___y_1017_, lean_box(0));
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; uint8_t v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_unbox(v_a_1060_);
lean_dec(v_a_1060_);
if (v___x_1061_ == 0)
{
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
v_a_1020_ = v_b_1015_;
goto v___jp_1019_;
}
else
{
lean_object* v_imports_1062_; lean_object* v_check_1063_; lean_object* v___y_1065_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_imports_1062_ = lean_ctor_get(v_snd_1028_, 3);
v_check_1063_ = lean_ctor_get(v_snd_1028_, 7);
v___x_1102_ = lean_array_get_size(v_imports_1062_);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8));
v___x_1104_ = lean_nat_dec_lt(v___x_1058_, v___x_1102_);
if (v___x_1104_ == 0)
{
v___y_1065_ = v___x_1103_;
goto v___jp_1064_;
}
else
{
size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = ((size_t)0ULL);
v___x_1106_ = lean_usize_of_nat(v___x_1102_);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_1011_, v_imports_1062_, v___x_1105_, v___x_1106_, v___x_1103_);
v___y_1065_ = v___x_1107_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_array_get_size(v___y_1065_);
v___x_1067_ = lean_nat_dec_eq(v___x_1066_, v___x_1058_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_del_object(v___x_1030_);
v___x_1068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1);
v___x_1069_ = lean_array_to_list(v___y_1065_);
v___x_1070_ = lean_box(0);
v___x_1071_ = l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(v___x_1069_, v___x_1070_);
v___x_1072_ = l_Lean_MessageData_ofList(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_snd_1028_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_fst_1027_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_array_push(v_b_1015_, v___x_1077_);
v_a_1020_ = v___x_1078_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec_ref(v___y_1065_);
v___x_1079_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1063_);
v___x_1080_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_1009_, v___x_1079_);
if (lean_obj_tag(v___x_1080_) == 1)
{
lean_object* v_val_1081_; 
lean_dec(v___x_1079_);
v_val_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v_val_1033_ = v_val_1081_;
v___y_1034_ = v___y_1016_;
v___y_1035_ = v___y_1017_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v___x_1080_);
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1010_, v___x_1079_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; 
lean_dec(v___x_1079_);
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_val_1083_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_val_1033_ = v_a_1085_;
v___y_1034_ = v___y_1016_;
v___y_1035_ = v___y_1017_;
goto v___jp_1032_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec_ref(v_b_1015_);
lean_dec_ref(v_shouldCheck_1008_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v___x_1082_);
lean_del_object(v___x_1030_);
v___x_1094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5);
v___x_1095_ = l_Lean_MessageData_ofName(v___x_1079_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_snd_1028_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_fst_1027_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_array_push(v_b_1015_, v___x_1100_);
v_a_1020_ = v___x_1101_;
goto v___jp_1019_;
}
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec_ref(v_b_1015_);
lean_dec_ref(v_shouldCheck_1008_);
v_a_1108_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1059_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1059_);
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
v___jp_1032_:
{
lean_object* v_check_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_check_1036_ = lean_ctor_get(v_snd_1028_, 7);
lean_inc(v_check_1036_);
v___x_1037_ = lean_apply_1(v_val_1033_, v_check_1036_);
lean_inc(v_snd_1028_);
v___x_1038_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_snd_1028_, v___x_1037_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
v_a_1020_ = v_b_1015_;
goto v___jp_1019_;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1057_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_Exception_isInterrupt(v_a_1039_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
lean_inc(v_a_1039_);
v___x_1044_ = l_Lean_Exception_isRuntime(v_a_1039_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_del_object(v___x_1041_);
v___x_1045_ = l_Lean_Exception_toMessageData(v_a_1039_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1045_);
lean_ctor_set(v___x_1030_, 0, v_snd_1028_);
v___x_1047_ = v___x_1030_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_snd_1028_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_fst_1027_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_array_push(v_b_1015_, v___x_1048_);
v_a_1020_ = v___x_1049_;
goto v___jp_1019_;
}
}
else
{
lean_object* v___x_1052_; 
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec_ref(v_b_1015_);
lean_dec_ref(v_shouldCheck_1008_);
if (v_isShared_1042_ == 0)
{
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1039_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v___x_1055_; 
lean_del_object(v___x_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec_ref(v_b_1015_);
lean_dec_ref(v_shouldCheck_1008_);
if (v_isShared_1042_ == 0)
{
v___x_1055_ = v___x_1041_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1039_);
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
}
}
}
v___jp_1019_:
{
size_t v___x_1021_; size_t v___x_1022_; 
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_1014_, v___x_1021_);
v_i_1014_ = v___x_1022_;
v_b_1015_ = v_a_1020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___boxed(lean_object* v_shouldCheck_1117_, lean_object* v_val_1118_, lean_object* v___x_1119_, lean_object* v___y_1120_, lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
size_t v_sz_boxed_1128_; size_t v_i_boxed_1129_; lean_object* v_res_1130_; 
v_sz_boxed_1128_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1129_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1117_, v_val_1118_, v___x_1119_, v___y_1120_, v_as_1121_, v_sz_boxed_1128_, v_i_boxed_1129_, v_b_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v_as_1121_);
lean_dec(v___y_1120_);
lean_dec(v___x_1119_);
lean_dec(v_val_1118_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run(lean_object* v_inPackage_1133_, lean_object* v_shouldCheck_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_env_1140_; lean_object* v___x_1141_; lean_object* v_toEnvExtension_1142_; lean_object* v_asyncMode_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_moduleNames_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___y_1153_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1138_ = lean_box(1);
v___x_1139_ = lean_st_ref_get(v_a_1136_);
v_env_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref_n(v_env_1140_, 2);
lean_dec(v___x_1139_);
v___x_1141_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_1142_ = lean_ctor_get(v___x_1141_, 0);
v_asyncMode_1143_ = lean_ctor_get(v_toEnvExtension_1142_, 2);
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1138_, v___x_1141_, v_env_1140_, v_asyncMode_1143_, v___x_1144_);
v___x_1146_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_1147_ = lean_st_ref_get(v___x_1146_);
v___x_1148_ = l_Lean_Environment_header(v_env_1140_);
v_moduleNames_1149_ = lean_ctor_get(v___x_1148_, 4);
lean_inc_ref(v_moduleNames_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Lean_NameSet_empty;
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_array_get_size(v_moduleNames_1149_);
v___x_1160_ = lean_nat_dec_lt(v___x_1151_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec_ref(v_moduleNames_1149_);
v___y_1153_ = v___x_1150_;
goto v___jp_1152_;
}
else
{
size_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = ((size_t)0ULL);
v___x_1162_ = lean_usize_of_nat(v___x_1159_);
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_moduleNames_1149_, v___x_1161_, v___x_1162_, v___x_1150_);
lean_dec_ref(v_moduleNames_1149_);
v___y_1153_ = v___x_1163_;
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1154_ = ((lean_object*)(l_Lean_Doc_DeferredCheck_run___closed__0));
v___x_1155_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(v_env_1140_, v_inPackage_1133_);
v_sz_1156_ = lean_array_size(v___x_1155_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1134_, v___x_1147_, v___x_1145_, v___y_1153_, v___x_1155_, v_sz_1156_, v___x_1157_, v___x_1154_, v_a_1135_, v_a_1136_);
lean_dec_ref(v___x_1155_);
lean_dec(v___y_1153_);
lean_dec(v___x_1145_);
lean_dec(v___x_1147_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run___boxed(lean_object* v_inPackage_1164_, lean_object* v_shouldCheck_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Doc_DeferredCheck_run(v_inPackage_1164_, v_shouldCheck_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1169_;
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
