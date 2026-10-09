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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_59_;
v_res_59_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_();
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3257731387____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_m_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v___x_81_; 
v_fst_79_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_fst_79_);
v_snd_80_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_snd_80_);
lean_dec_ref(v_x_78_);
v___x_81_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_79_, v_snd_80_, v_m_77_);
return v___x_81_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_82_, size_t v_i_83_, size_t v_stop_84_, lean_object* v_b_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = lean_usize_dec_eq(v_i_83_, v_stop_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v_fst_88_; lean_object* v_snd_89_; lean_object* v___x_90_; size_t v___x_91_; size_t v___x_92_; 
v___x_87_ = lean_array_uget_borrowed(v_as_82_, v_i_83_);
v_fst_88_ = lean_ctor_get(v___x_87_, 0);
v_snd_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_snd_89_);
lean_inc(v_fst_88_);
v___x_90_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_88_, v_snd_89_, v_b_85_);
v___x_91_ = ((size_t)1ULL);
v___x_92_ = lean_usize_add(v_i_83_, v___x_91_);
v_i_83_ = v___x_92_;
v_b_85_ = v___x_90_;
goto _start;
}
else
{
return v_b_85_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_82_ = stack[0].m_obj;
size_t v_i_83_ = stack[1].m_num;
size_t v_stop_84_ = stack[2].m_num;
lean_object* v_b_85_ = stack[3].m_obj;
lean_object* v_res_94_;
v_res_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(v_as_82_, v_i_83_, v_stop_84_, v_b_85_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_95_, lean_object* v_i_96_, lean_object* v_stop_97_, lean_object* v_b_98_){
_start:
{
size_t v_i_boxed_99_; size_t v_stop_boxed_100_; lean_object* v_res_101_; 
v_i_boxed_99_ = lean_unbox_usize(v_i_96_);
lean_dec(v_i_96_);
v_stop_boxed_100_ = lean_unbox_usize(v_stop_97_);
lean_dec(v_stop_97_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(v_as_95_, v_i_boxed_99_, v_stop_boxed_100_, v_b_98_);
lean_dec_ref(v_as_95_);
return v_res_101_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(lean_object* v_as_102_, size_t v_i_103_, size_t v_stop_104_, lean_object* v_b_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_103_, v_stop_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_107_ = lean_array_uget_borrowed(v_as_102_, v_i_103_);
v_fst_108_ = lean_ctor_get(v___x_107_, 0);
v_snd_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_snd_109_);
lean_inc(v_fst_108_);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_108_, v_snd_109_, v_b_105_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_103_, v___x_111_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_spec__0(v_as_102_, v___x_112_, v_stop_104_, v___x_110_);
return v___x_113_;
}
else
{
return v_b_105_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_102_ = stack[0].m_obj;
size_t v_i_103_ = stack[1].m_num;
size_t v_stop_104_ = stack[2].m_num;
lean_object* v_b_105_ = stack[3].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v_as_102_, v_i_103_, v_stop_104_, v_b_105_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_115_, lean_object* v_i_116_, lean_object* v_stop_117_, lean_object* v_b_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_stop_boxed_120_; lean_object* v_res_121_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_116_);
lean_dec(v_i_116_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_117_);
lean_dec(v_stop_117_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v_as_115_, v_i_boxed_119_, v_stop_boxed_120_, v_b_118_);
lean_dec_ref(v_as_115_);
return v_res_121_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(lean_object* v_as_122_, size_t v_i_123_, size_t v_stop_124_, lean_object* v_b_125_){
_start:
{
lean_object* v___y_127_; uint8_t v___x_131_; 
v___x_131_ = lean_usize_dec_eq(v_i_123_, v_stop_124_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_132_ = lean_array_uget_borrowed(v_as_122_, v_i_123_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v___x_132_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
v___y_127_ = v_b_125_;
goto v___jp_126_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_le(v___x_134_, v___x_134_);
if (v___x_136_ == 0)
{
if (v___x_135_ == 0)
{
v___y_127_ = v_b_125_;
goto v___jp_126_;
}
else
{
size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_134_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v___x_132_, v___x_137_, v___x_138_, v_b_125_);
v___y_127_ = v___x_139_;
goto v___jp_126_;
}
}
else
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_134_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__0(v___x_132_, v___x_140_, v___x_141_, v_b_125_);
v___y_127_ = v___x_142_;
goto v___jp_126_;
}
}
}
else
{
return v_b_125_;
}
v___jp_126_:
{
size_t v___x_128_; size_t v___x_129_; 
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_123_, v___x_128_);
v_i_123_ = v___x_129_;
v_b_125_ = v___y_127_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_122_ = stack[0].m_obj;
size_t v_i_123_ = stack[1].m_num;
size_t v_stop_124_ = stack[2].m_num;
lean_object* v_b_125_ = stack[3].m_obj;
lean_object* v_res_143_;
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_as_122_, v_i_123_, v_stop_124_, v_b_125_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_144_, lean_object* v_i_145_, lean_object* v_stop_146_, lean_object* v_b_147_){
_start:
{
size_t v_i_boxed_148_; size_t v_stop_boxed_149_; lean_object* v_res_150_; 
v_i_boxed_148_ = lean_unbox_usize(v_i_145_);
lean_dec(v_i_145_);
v_stop_boxed_149_ = lean_unbox_usize(v_stop_146_);
lean_dec(v_stop_146_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_as_144_, v_i_boxed_148_, v_stop_boxed_149_, v_b_147_);
lean_dec_ref(v_as_144_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_nss_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_box(1);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_array_get_size(v_nss_151_);
v___x_155_ = lean_nat_dec_lt(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
return v___x_152_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_le(v___x_154_, v___x_154_);
if (v___x_156_ == 0)
{
if (v___x_155_ == 0)
{
return v___x_152_;
}
else
{
size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((size_t)0ULL);
v___x_158_ = lean_usize_of_nat(v___x_154_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_nss_151_, v___x_157_, v___x_158_, v___x_152_);
return v___x_159_;
}
}
else
{
size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((size_t)0ULL);
v___x_161_ = lean_usize_of_nat(v___x_154_);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__spec__1(v_nss_151_, v___x_160_, v___x_161_, v___x_152_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_nss_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(v_nss_163_);
lean_dec_ref(v_nss_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(lean_object* v_es_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_array_mk(v_es_165_);
return v___x_166_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_));
v___x_187_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_188_;
v_res_188_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2____boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3792406048____hygCtx___hyg_2_();
return v_res_190_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(1);
v___x_193_ = lean_st_mk_ref(v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_195_;
v_res_195_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2____boxed(lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_3985216099____hygCtx___hyg_2_();
return v_res_197_;
}
}
lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler(lean_object* v_key_198_, lean_object* v_impl_199_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_202_ = lean_st_ref_take(v___x_201_);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_key_198_, v_impl_199_, v___x_202_);
v___x_204_ = lean_st_ref_put(v___x_201_, v___x_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT void l_Lean_Doc_DeferredCheck_addBuiltinHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_198_ = stack[0].m_obj;
lean_object* v_impl_199_ = stack[1].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_Lean_Doc_DeferredCheck_addBuiltinHandler(v_key_198_, v_impl_199_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_addBuiltinHandler___boxed(lean_object* v_key_207_, lean_object* v_impl_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Doc_DeferredCheck_addBuiltinHandler(v_key_207_, v_impl_208_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
lean_ctor_set(v___x_217_, 4, v___x_215_);
lean_ctor_set(v___x_217_, 5, v___x_215_);
lean_ctor_set(v___x_217_, 6, v___x_215_);
lean_ctor_set(v___x_217_, 7, v___x_215_);
lean_ctor_set(v___x_217_, 8, v___x_215_);
lean_ctor_set(v___x_217_, 9, v___x_215_);
lean_ctor_set(v___x_217_, 10, v___x_215_);
lean_ctor_set(v___x_217_, 11, v___x_214_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(32u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_unsigned_to_nat(32u);
v___x_224_ = lean_mk_empty_array_with_capacity(v___x_223_);
v___x_225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_226_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_222_);
lean_ctor_set(v___x_226_, 3, v___x_222_);
lean_ctor_set_usize(v___x_226_, 4, v___x_221_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_box(1);
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v_toCold_236_; lean_object* v_env_237_; lean_object* v_options_238_; uint8_t v___x_239_; lean_object* v_env_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_toCold_236_ = lean_ctor_get(v___y_232_, 0);
v_env_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_235_);
v_options_238_ = lean_ctor_get(v_toCold_236_, 2);
v___x_239_ = 0;
v_env_240_ = l_Lean_Environment_setRecordingDeps(v_env_237_, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_238_);
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v_env_240_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
lean_ctor_set(v___x_243_, 3, v_options_238_);
v___x_244_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_msgData_231_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_231_ = stack[0].m_obj;
lean_object* v___y_232_ = stack[1].m_obj;
lean_object* v___y_233_ = stack[2].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_ref_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_ref_256_ = lean_ctor_get(v___y_253_, 2);
v___x_257_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_252_, v___y_253_, v___y_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_ref_256_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_ref_256_);
lean_ctor_set(v___x_262_, 1, v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_252_ = stack[0].m_obj;
lean_object* v___y_253_ = stack[1].m_obj;
lean_object* v___y_254_ = stack[2].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_252_, v___y_253_, v___y_254_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_272_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_a_277_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v_x_273_, 1);
v___x_278_ = l_Lean_stringToMessageData(v_a_277_);
v___x_279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_278_, v___y_274_, v___y_275_);
return v___x_279_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_a_280_ = lean_ctor_get(v_x_273_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v_x_273_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v_x_273_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 0);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_273_ = stack[0].m_obj;
lean_object* v___y_274_ = stack[1].m_obj;
lean_object* v___y_275_ = stack[2].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
v___x_295_ = l_Lean_Elab_abortCommandExceptionId;
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
return v___x_296_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_300_;
v_res_300_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v_res_302_;
}
}
lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(lean_object* v_typeName_303_, lean_object* v_constName_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v_env_309_; uint8_t v___x_310_; 
v___x_308_ = lean_st_ref_get(v___y_306_);
v_env_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_env_309_);
lean_dec(v___x_308_);
lean_inc(v_constName_304_);
v___x_310_ = lean_has_compile_error(v_env_309_, v_constName_304_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_311_ = lean_st_ref_get(v___y_306_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_305_);
v___x_314_ = l_Lean_Environment_evalConstCheck___redArg(v_env_312_, v___x_313_, v_typeName_303_, v_constName_304_);
lean_dec_ref(v___x_313_);
v___x_315_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_314_, v___y_305_, v___y_306_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec_ref_known(v___x_316_, 1);
v___x_317_ = lean_st_ref_get(v___y_306_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_305_);
v___x_320_ = l_Lean_Environment_evalConstCheck___redArg(v_env_318_, v___x_319_, v_typeName_303_, v_constName_304_);
lean_dec_ref(v___x_319_);
v___x_321_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_320_, v___y_305_, v___y_306_);
return v___x_321_;
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_constName_304_);
lean_dec(v_typeName_303_);
v_a_322_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_316_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_316_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_303_ = stack[0].m_obj;
lean_object* v_constName_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_303_, v_constName_304_, v___y_305_, v___y_306_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_331_, lean_object* v_constName_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_331_, v_constName_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_336_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(lean_object* v_declName_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___closed__1));
v___x_347_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v___x_346_, v_declName_342_, v_a_343_, v_a_344_);
return v___x_347_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_342_ = stack[0].m_obj;
lean_object* v_a_343_ = stack[1].m_obj;
lean_object* v_a_344_ = stack[2].m_obj;
lean_object* v_res_348_;
v_res_348_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_declName_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe___boxed(lean_object* v_declName_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_declName_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_353_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___redArg();
return v___x_358_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_355_ = stack[1].m_obj;
lean_object* v___y_356_ = stack[2].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(lean_box(0), v___y_355_, v___y_356_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_364_;
}
}
lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_object* v_00_u03b1_365_, lean_object* v_typeName_366_, lean_object* v_constName_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___redArg(v_typeName_366_, v_constName_367_, v___y_368_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT void l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_366_ = stack[1].m_obj;
lean_object* v_constName_367_ = stack[2].m_obj;
lean_object* v___y_368_ = stack[3].m_obj;
lean_object* v___y_369_ = stack[4].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(lean_box(0), v_typeName_366_, v_constName_367_, v___y_368_, v___y_369_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_373_, lean_object* v_typeName_374_, lean_object* v_constName_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0(v_00_u03b1_373_, v_typeName_374_, v_constName_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_381_, v___y_382_, v___y_383_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_381_ = stack[1].m_obj;
lean_object* v___y_382_ = stack[2].m_obj;
lean_object* v___y_383_ = stack[3].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(lean_box(0), v_x_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_387_, lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_387_, v_x_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_392_;
}
}
lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_394_, v___y_395_, v___y_396_);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_394_ = stack[1].m_obj;
lean_object* v___y_395_ = stack[2].m_obj;
lean_object* v___y_396_ = stack[3].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_box(0), v_msg_394_, v___y_395_, v___y_396_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_400_, v_msg_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v_s_408_){
_start:
{
lean_object* v_addEntryFn_409_; lean_object* v_importedEntries_410_; lean_object* v_state_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_addEntryFn_409_ = lean_ctor_get(v___x_406_, 3);
lean_inc(v_addEntryFn_409_);
lean_dec_ref(v___x_406_);
v_importedEntries_410_ = lean_ctor_get(v_s_408_, 0);
v_state_411_ = lean_ctor_get(v_s_408_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_s_408_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v_s_408_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_state_411_);
lean_inc(v_importedEntries_410_);
lean_dec(v_s_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_state_415_; lean_object* v___x_417_; 
v_state_415_ = lean_apply_2(v_addEntryFn_409_, v_state_411_, v___x_407_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_state_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_importedEntries_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_state_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__5_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__7_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_decl_437_, lean_object* v_stx_438_, uint8_t v_kind_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___y_444_; lean_object* v_nextMacroScope_445_; lean_object* v_ngen_446_; lean_object* v_auxDeclNGen_447_; lean_object* v_traceState_448_; lean_object* v_recordedDeps_449_; lean_object* v_messages_450_; lean_object* v_infoState_451_; lean_object* v_snapshotTasks_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v_key_460_; lean_object* v___y_461_; uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 0;
v___x_536_ = l_Lean_instBEqAttributeKind_beq(v_kind_439_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_stx_438_);
lean_dec(v_decl_437_);
lean_dec_ref(v___x_434_);
lean_dec(v___x_433_);
v___x_537_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__8_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_538_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_537_, v___y_440_, v___y_441_);
return v___x_538_;
}
else
{
goto v___jp_483_;
}
v___jp_443_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v_nextMacroScope_445_);
lean_ctor_set(v___x_456_, 2, v_ngen_446_);
lean_ctor_set(v___x_456_, 3, v_auxDeclNGen_447_);
lean_ctor_set(v___x_456_, 4, v_traceState_448_);
lean_ctor_set(v___x_456_, 5, v___x_455_);
lean_ctor_set(v___x_456_, 6, v_recordedDeps_449_);
lean_ctor_set(v___x_456_, 7, v_messages_450_);
lean_ctor_set(v___x_456_, 8, v_infoState_451_);
lean_ctor_set(v___x_456_, 9, v_snapshotTasks_452_);
v___x_457_ = lean_st_ref_put(v___y_444_, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___y_453_);
return v___x_458_;
}
v___jp_459_:
{
lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_traceState_467_; lean_object* v_recordedDeps_468_; lean_object* v_messages_469_; lean_object* v_infoState_470_; lean_object* v_snapshotTasks_471_; lean_object* v___x_472_; lean_object* v_toEnvExtension_473_; lean_object* v_asyncMode_474_; uint8_t v_logWrites_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___f_478_; uint8_t v___x_479_; 
v___x_462_ = lean_st_ref_take(v___y_461_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_463_);
v_nextMacroScope_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_nextMacroScope_464_);
v_ngen_465_ = lean_ctor_get(v___x_462_, 2);
lean_inc_ref(v_ngen_465_);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_462_, 3);
lean_inc_ref(v_auxDeclNGen_466_);
v_traceState_467_ = lean_ctor_get(v___x_462_, 4);
lean_inc_ref(v_traceState_467_);
v_recordedDeps_468_ = lean_ctor_get(v___x_462_, 6);
lean_inc_ref(v_recordedDeps_468_);
v_messages_469_ = lean_ctor_get(v___x_462_, 7);
lean_inc_ref(v_messages_469_);
v_infoState_470_ = lean_ctor_get(v___x_462_, 8);
lean_inc_ref(v_infoState_470_);
v_snapshotTasks_471_ = lean_ctor_get(v___x_462_, 9);
lean_inc_ref(v_snapshotTasks_471_);
lean_dec(v___x_462_);
v___x_472_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_473_ = lean_ctor_get(v___x_472_, 0);
v_asyncMode_474_ = lean_ctor_get(v_toEnvExtension_473_, 2);
v_logWrites_475_ = lean_ctor_get_uint8(v_toEnvExtension_473_, sizeof(void*)*6);
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_key_460_);
lean_ctor_set(v___x_477_, 1, v_decl_437_);
v___f_478_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_478_, 0, v___x_472_);
lean_closure_set(v___f_478_, 1, v___x_477_);
v___x_479_ = 1;
if (v_logWrites_475_ == 0)
{
lean_object* v___x_480_; 
lean_inc_ref(v_toEnvExtension_473_);
v___x_480_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_473_, v_env_463_, v___f_478_, v_asyncMode_474_, v___x_433_, v___x_479_);
v___y_444_ = v___y_461_;
v_nextMacroScope_445_ = v_nextMacroScope_464_;
v_ngen_446_ = v_ngen_465_;
v_auxDeclNGen_447_ = v_auxDeclNGen_466_;
v_traceState_448_ = v_traceState_467_;
v_recordedDeps_449_ = v_recordedDeps_468_;
v_messages_450_ = v_messages_469_;
v_infoState_451_ = v_infoState_470_;
v_snapshotTasks_452_ = v_snapshotTasks_471_;
v___y_453_ = v___x_476_;
v___y_454_ = v___x_480_;
goto v___jp_443_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc_ref_n(v_toEnvExtension_473_, 2);
v___x_481_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_473_, v_env_463_);
lean_dec_ref(v_env_463_);
v___x_482_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_473_, v___x_481_, v___f_478_, v_asyncMode_474_, v___x_433_, v___x_479_);
v___y_444_ = v___y_461_;
v_nextMacroScope_445_ = v_nextMacroScope_464_;
v_ngen_446_ = v_ngen_465_;
v_auxDeclNGen_447_ = v_auxDeclNGen_466_;
v_traceState_448_ = v_traceState_467_;
v_recordedDeps_449_ = v_recordedDeps_468_;
v_messages_450_ = v_messages_469_;
v_infoState_451_ = v_infoState_470_;
v_snapshotTasks_452_ = v_snapshotTasks_471_;
v___y_453_ = v___x_476_;
v___y_454_ = v___x_482_;
goto v___jp_443_;
}
}
v___jp_483_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_487_ = l_Lean_Name_mkStr4(v___x_434_, v___x_484_, v___x_485_, v___x_486_);
lean_inc(v_stx_438_);
v___x_488_ = l_Lean_Syntax_isOfKind(v_stx_438_, v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_stx_438_);
lean_dec(v_decl_437_);
lean_dec(v___x_433_);
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_490_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_489_, v___y_440_, v___y_441_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = l_Lean_Syntax_getArg(v_stx_438_, v___x_435_);
v___x_500_ = l_Lean_Syntax_matchesIdent(v___x_499_, v___x_436_);
lean_dec(v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_stx_438_);
lean_dec(v_decl_437_);
lean_dec(v___x_433_);
v___x_501_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_502_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_501_, v___y_440_, v___y_441_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = l_Lean_Syntax_getArg(v_stx_438_, v___x_511_);
lean_dec(v_stx_438_);
lean_inc(v___x_512_);
v___x_513_ = l_Lean_Syntax_matchesNull(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v___x_512_);
lean_dec(v_decl_437_);
lean_dec(v___x_433_);
v___x_514_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__6_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_515_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_514_, v___y_440_, v___y_441_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_Syntax_getArg(v___x_512_, v___x_435_);
lean_dec(v___x_512_);
v___x_525_ = l_Lean_realizeGlobalConstNoOverload(v___x_524_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_key_460_ = v_a_526_;
v___y_461_ = v___y_441_;
goto v___jp_459_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_decl_437_);
lean_dec(v___x_433_);
v_a_527_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_433_ = stack[0].m_obj;
lean_object* v___x_434_ = stack[1].m_obj;
lean_object* v___x_435_ = stack[2].m_obj;
lean_object* v___x_436_ = stack[3].m_obj;
lean_object* v_decl_437_ = stack[4].m_obj;
lean_object* v_stx_438_ = stack[5].m_obj;
uint8_t v_kind_439_ = stack[6].m_num;
lean_object* v___y_440_ = stack[7].m_obj;
lean_object* v___y_441_ = stack[8].m_obj;
lean_object* v_res_539_;
v_res_539_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_433_, v___x_434_, v___x_435_, v___x_436_, v_decl_437_, v_stx_438_, v_kind_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_decl_544_, lean_object* v_stx_545_, lean_object* v_kind_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v_kind_boxed_550_; lean_object* v_res_551_; 
v_kind_boxed_550_ = lean_unbox(v_kind_546_);
v_res_551_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_540_, v___x_541_, v___x_542_, v___x_543_, v_decl_544_, v_stx_545_, v_kind_boxed_550_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___x_543_);
lean_dec(v___x_542_);
return v_res_551_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(lean_object* v___x_558_, lean_object* v_decl_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_564_ = l_Lean_MessageData_ofName(v___x_558_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_567_, v___y_560_, v___y_561_);
return v___x_568_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_558_ = stack[0].m_obj;
lean_object* v_decl_559_ = stack[1].m_obj;
lean_object* v___y_560_ = stack[2].m_obj;
lean_object* v___y_561_ = stack[3].m_obj;
lean_object* v_res_569_;
v_res_569_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_558_, v_decl_559_, v___y_560_, v___y_561_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v___x_570_, lean_object* v_decl_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(v___x_570_, v_decl_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v_decl_571_);
return v_res_575_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__36_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_670_ = l_Lean_registerBuiltinAttribute(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_671_;
v_res_671_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2____boxed(lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_();
return v_res_673_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v___x_683_, lean_object* v___x_684_, lean_object* v___x_685_, lean_object* v_decl_686_, lean_object* v_stx_687_, uint8_t v_kind_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_key_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 0;
v___x_757_ = l_Lean_instBEqAttributeKind_beq(v_kind_688_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_stx_687_);
lean_dec(v_decl_686_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_681_);
v___x_758_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_759_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_758_, v___y_689_, v___y_690_);
return v___x_759_;
}
else
{
goto v___jp_704_;
}
v___jp_692_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_697_ = l_Lean_Name_mkStr4(v___x_681_, v___x_682_, v___x_683_, v___x_696_);
v___x_698_ = lean_box(0);
v___x_699_ = l_Lean_Expr_const___override(v___x_697_, v___x_698_);
v___x_700_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_key_693_);
lean_inc(v_decl_686_);
v___x_701_ = l_Lean_Expr_const___override(v_decl_686_, v___x_698_);
v___x_702_ = l_Lean_mkAppB(v___x_699_, v___x_700_, v___x_701_);
v___x_703_ = l_Lean_declareBuiltin(v_decl_686_, v___x_702_, v___y_694_, v___y_695_);
return v___x_703_;
}
v___jp_704_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__3_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__1___closed__4_00___x40_Lean_Elab_DocString_Builtin_Postponed_1993970768____hygCtx___hyg_2_));
lean_inc_ref(v___x_681_);
v___x_708_ = l_Lean_Name_mkStr4(v___x_681_, v___x_705_, v___x_706_, v___x_707_);
lean_inc(v_stx_687_);
v___x_709_ = l_Lean_Syntax_isOfKind(v_stx_687_, v___x_708_);
lean_dec(v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_stx_687_);
lean_dec(v_decl_686_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_681_);
v___x_710_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_711_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_710_, v___y_689_, v___y_690_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Syntax_getArg(v_stx_687_, v___x_684_);
v___x_721_ = l_Lean_Syntax_matchesIdent(v___x_720_, v___x_685_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_stx_687_);
lean_dec(v_decl_686_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_681_);
v___x_722_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_723_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_722_, v___y_689_, v___y_690_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = l_Lean_Syntax_getArg(v_stx_687_, v___x_732_);
lean_dec(v_stx_687_);
lean_inc(v___x_733_);
v___x_734_ = l_Lean_Syntax_matchesNull(v___x_733_, v___x_732_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___x_733_);
lean_dec(v_decl_686_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_681_);
v___x_735_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_, &l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0___closed__2_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_);
v___x_736_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_735_, v___y_689_, v___y_690_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_Lean_Syntax_getArg(v___x_733_, v___x_684_);
lean_dec(v___x_733_);
v___x_746_ = l_Lean_realizeGlobalConstNoOverload(v___x_745_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v_key_693_ = v_a_747_;
v___y_694_ = v___y_689_;
v___y_695_ = v___y_690_;
goto v___jp_692_;
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_decl_686_);
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_681_);
v_a_748_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_746_);
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
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_681_ = stack[0].m_obj;
lean_object* v___x_682_ = stack[1].m_obj;
lean_object* v___x_683_ = stack[2].m_obj;
lean_object* v___x_684_ = stack[3].m_obj;
lean_object* v___x_685_ = stack[4].m_obj;
lean_object* v_decl_686_ = stack[5].m_obj;
lean_object* v_stx_687_ = stack[6].m_obj;
uint8_t v_kind_688_ = stack[7].m_num;
lean_object* v___y_689_ = stack[8].m_obj;
lean_object* v___y_690_ = stack[9].m_obj;
lean_object* v_res_760_;
v_res_760_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(v___x_681_, v___x_682_, v___x_683_, v___x_684_, v___x_685_, v_decl_686_, v_stx_687_, v_kind_688_, v___y_689_, v___y_690_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v___x_765_, lean_object* v_decl_766_, lean_object* v_stx_767_, lean_object* v_kind_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint8_t v_kind_boxed_772_; lean_object* v_res_773_; 
v_kind_boxed_772_ = lean_unbox(v_kind_768_);
v_res_773_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___lam__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(v___x_761_, v___x_762_, v___x_763_, v___x_764_, v___x_765_, v_decl_766_, v_stx_767_, v_kind_boxed_772_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___x_765_);
lean_dec(v___x_764_);
return v_res_773_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn___closed__10_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_));
v___x_809_ = l_Lean_registerBuiltinAttribute(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2____boxed(lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_initFn_00___x40_Lean_Elab_DocString_Builtin_Postponed_195487833____hygCtx___hyg_2_();
return v_res_812_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(lean_object* v_c_813_, lean_object* v_act_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_currNamespace_818_; lean_object* v_openDecls_819_; lean_object* v_options_820_; lean_object* v___x_821_; lean_object* v_toCold_822_; lean_object* v_currRecDepth_823_; lean_object* v_ref_824_; uint16_t v_optionFlags_825_; uint8_t v_suppressElabErrors_826_; uint8_t v_isRecordingDeps_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_854_; 
v_currNamespace_818_ = lean_ctor_get(v_c_813_, 4);
lean_inc(v_currNamespace_818_);
v_openDecls_819_ = lean_ctor_get(v_c_813_, 5);
lean_inc(v_openDecls_819_);
v_options_820_ = lean_ctor_get(v_c_813_, 6);
lean_inc_ref(v_options_820_);
lean_dec_ref(v_c_813_);
lean_inc_ref(v_a_815_);
v___x_821_ = l_Lean_Core_Context_setOptions(v_a_815_, v_options_820_);
v_toCold_822_ = lean_ctor_get(v___x_821_, 0);
v_currRecDepth_823_ = lean_ctor_get(v___x_821_, 1);
v_ref_824_ = lean_ctor_get(v___x_821_, 2);
v_optionFlags_825_ = lean_ctor_get_uint16(v___x_821_, sizeof(void*)*3);
v_suppressElabErrors_826_ = lean_ctor_get_uint8(v___x_821_, sizeof(void*)*3 + 2);
v_isRecordingDeps_827_ = lean_ctor_get_uint8(v___x_821_, sizeof(void*)*3 + 3);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_854_ == 0)
{
v___x_829_ = v___x_821_;
v_isShared_830_ = v_isSharedCheck_854_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_ref_824_);
lean_inc(v_currRecDepth_823_);
lean_inc(v_toCold_822_);
lean_dec(v___x_821_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_854_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fileName_831_; lean_object* v_fileMap_832_; lean_object* v_options_833_; lean_object* v_maxRecDepth_834_; lean_object* v_initHeartbeats_835_; lean_object* v_maxHeartbeats_836_; lean_object* v_quotContext_837_; lean_object* v_currMacroScope_838_; lean_object* v_cancelTk_x3f_839_; lean_object* v_inheritedTraceOptions_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v_fileName_831_ = lean_ctor_get(v_toCold_822_, 0);
v_fileMap_832_ = lean_ctor_get(v_toCold_822_, 1);
v_options_833_ = lean_ctor_get(v_toCold_822_, 2);
v_maxRecDepth_834_ = lean_ctor_get(v_toCold_822_, 3);
v_initHeartbeats_835_ = lean_ctor_get(v_toCold_822_, 6);
v_maxHeartbeats_836_ = lean_ctor_get(v_toCold_822_, 7);
v_quotContext_837_ = lean_ctor_get(v_toCold_822_, 8);
v_currMacroScope_838_ = lean_ctor_get(v_toCold_822_, 9);
v_cancelTk_x3f_839_ = lean_ctor_get(v_toCold_822_, 10);
v_inheritedTraceOptions_840_ = lean_ctor_get(v_toCold_822_, 11);
v_isSharedCheck_851_ = !lean_is_exclusive(v_toCold_822_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; 
v_unused_852_ = lean_ctor_get(v_toCold_822_, 5);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_toCold_822_, 4);
lean_dec(v_unused_853_);
v___x_842_ = v_toCold_822_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_inheritedTraceOptions_840_);
lean_inc(v_cancelTk_x3f_839_);
lean_inc(v_currMacroScope_838_);
lean_inc(v_quotContext_837_);
lean_inc(v_maxHeartbeats_836_);
lean_inc(v_initHeartbeats_835_);
lean_inc(v_maxRecDepth_834_);
lean_inc(v_options_833_);
lean_inc(v_fileMap_832_);
lean_inc(v_fileName_831_);
lean_dec(v_toCold_822_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 5, v_openDecls_819_);
lean_ctor_set(v___x_842_, 4, v_currNamespace_818_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fileName_831_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_fileMap_832_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_options_833_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_maxRecDepth_834_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_currNamespace_818_);
lean_ctor_set(v_reuseFailAlloc_850_, 5, v_openDecls_819_);
lean_ctor_set(v_reuseFailAlloc_850_, 6, v_initHeartbeats_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 7, v_maxHeartbeats_836_);
lean_ctor_set(v_reuseFailAlloc_850_, 8, v_quotContext_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 9, v_currMacroScope_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 10, v_cancelTk_x3f_839_);
lean_ctor_set(v_reuseFailAlloc_850_, 11, v_inheritedTraceOptions_840_);
v___x_845_ = v_reuseFailAlloc_850_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_845_);
v___x_847_ = v___x_829_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_currRecDepth_823_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_ref_824_);
lean_ctor_set_uint16(v_reuseFailAlloc_849_, sizeof(void*)*3, v_optionFlags_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*3 + 2, v_suppressElabErrors_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*3 + 3, v_isRecordingDeps_827_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
lean_inc(v_a_816_);
v___x_848_ = lean_apply_3(v_act_814_, v___x_847_, v_a_816_, lean_box(0));
return v___x_848_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_813_ = stack[0].m_obj;
lean_object* v_act_814_ = stack[1].m_obj;
lean_object* v_a_815_ = stack[2].m_obj;
lean_object* v_a_816_ = stack[3].m_obj;
lean_object* v_res_855_;
v_res_855_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_813_, v_act_814_, v_a_815_, v_a_816_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg___boxed(lean_object* v_c_856_, lean_object* v_act_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_856_, v_act_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_object* v_00_u03b1_862_, lean_object* v_c_863_, lean_object* v_act_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_c_863_, v_act_864_, v_a_865_, v_a_866_);
return v___x_868_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_863_ = stack[1].m_obj;
lean_object* v_act_864_ = stack[2].m_obj;
lean_object* v_a_865_ = stack[3].m_obj;
lean_object* v_a_866_ = stack[4].m_obj;
lean_object* v_res_869_;
v_res_869_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(lean_box(0), v_c_863_, v_act_864_, v_a_865_, v_a_866_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___boxed(lean_object* v_00_u03b1_870_, lean_object* v_c_871_, lean_object* v_act_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope(v_00_u03b1_870_, v_c_871_, v_act_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_876_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(lean_object* v___x_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_bs_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_881_ == 0)
{
lean_dec(v___x_877_);
return v_bs_880_;
}
else
{
lean_object* v_v_882_; lean_object* v___x_883_; lean_object* v_bs_x27_884_; lean_object* v___x_885_; size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
v_v_882_ = lean_array_uget(v_bs_880_, v_i_879_);
v___x_883_ = lean_unsigned_to_nat(0u);
v_bs_x27_884_ = lean_array_uset(v_bs_880_, v_i_879_, v___x_883_);
lean_inc(v___x_877_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_877_);
lean_ctor_set(v___x_885_, 1, v_v_882_);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_879_, v___x_886_);
v___x_888_ = lean_array_uset(v_bs_x27_884_, v_i_879_, v___x_885_);
v_i_879_ = v___x_887_;
v_bs_880_ = v___x_888_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_877_ = stack[0].m_obj;
size_t v_sz_878_ = stack[1].m_num;
size_t v_i_879_ = stack[2].m_num;
lean_object* v_bs_880_ = stack[3].m_obj;
lean_object* v_res_890_;
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_877_, v_sz_878_, v_i_879_, v_bs_880_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0___boxed(lean_object* v___x_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_bs_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_896_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_891_, v_sz_boxed_895_, v_i_boxed_896_, v_bs_894_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Array_instInhabited___redArg();
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(lean_object* v___x_899_, lean_object* v_inPackage_900_, lean_object* v_env_901_, lean_object* v_range_902_, lean_object* v_b_903_, lean_object* v_i_904_){
_start:
{
lean_object* v_stop_905_; lean_object* v_step_906_; lean_object* v_a_908_; uint8_t v___x_911_; 
v_stop_905_ = lean_ctor_get(v_range_902_, 1);
v_step_906_ = lean_ctor_get(v_range_902_, 2);
v___x_911_ = lean_nat_dec_lt(v_i_904_, v_stop_905_);
if (v___x_911_ == 0)
{
lean_dec(v_i_904_);
lean_dec_ref(v_inPackage_900_);
return v_b_903_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_array_get_borrowed(v___x_912_, v___x_899_, v_i_904_);
lean_inc_ref(v_inPackage_900_);
lean_inc(v___x_913_);
v___x_914_ = lean_apply_1(v_inPackage_900_, v___x_913_);
v___x_915_ = lean_unbox(v___x_914_);
if (v___x_915_ == 0)
{
v_a_908_ = v_b_903_;
goto v___jp_907_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_917_ = l_Lean_Doc_deferredCheckExt;
v___x_918_ = 0;
v___x_919_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_916_, v___x_917_, v_env_901_, v_i_904_, v___x_918_);
v_sz_920_ = lean_array_size(v___x_919_);
v___x_921_ = ((size_t)0ULL);
lean_inc(v___x_913_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_913_, v_sz_920_, v___x_921_, v___x_919_);
v___x_923_ = l_Array_append___redArg(v_b_903_, v___x_922_);
lean_dec_ref(v___x_922_);
v_a_908_ = v___x_923_;
goto v___jp_907_;
}
}
v___jp_907_:
{
lean_object* v___x_909_; 
v___x_909_ = lean_nat_add(v_i_904_, v_step_906_);
lean_dec(v_i_904_);
v_b_903_ = v_a_908_;
v_i_904_ = v___x_909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___boxed(lean_object* v___x_924_, lean_object* v_inPackage_925_, lean_object* v_env_926_, lean_object* v_range_927_, lean_object* v_b_928_, lean_object* v_i_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_924_, v_inPackage_925_, v_env_926_, v_range_927_, v_b_928_, v_i_929_);
lean_dec_ref(v_range_927_);
lean_dec_ref(v_env_926_);
lean_dec_ref(v___x_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(lean_object* v_env_933_, lean_object* v_inPackage_934_){
_start:
{
lean_object* v___x_935_; lean_object* v_moduleNames_936_; lean_object* v___x_937_; lean_object* v_out_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_935_ = l_Lean_Environment_header(v_env_933_);
v_moduleNames_936_ = lean_ctor_get(v___x_935_, 4);
lean_inc_ref(v_moduleNames_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = lean_unsigned_to_nat(0u);
v_out_938_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect___closed__0));
v___x_939_ = lean_array_get_size(v_moduleNames_936_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_937_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
lean_inc_ref(v_inPackage_934_);
v___x_942_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v_moduleNames_936_, v_inPackage_934_, v_env_933_, v___x_941_, v_out_938_, v___x_937_);
lean_dec_ref_known(v___x_941_, 3);
lean_dec_ref(v_moduleNames_936_);
v___x_943_ = l_Lean_Environment_mainModule(v_env_933_);
lean_inc(v___x_943_);
v___x_944_ = lean_apply_1(v_inPackage_934_, v___x_943_);
v___x_945_ = lean_unbox(v___x_944_);
if (v___x_945_ == 0)
{
lean_dec(v___x_943_);
lean_dec_ref(v_env_933_);
return v___x_942_;
}
else
{
lean_object* v___x_946_; lean_object* v_toEnvExtension_947_; lean_object* v_asyncMode_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; size_t v_sz_953_; size_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_946_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_947_ = lean_ctor_get(v___x_946_, 0);
v_asyncMode_948_ = lean_ctor_get(v_toEnvExtension_947_, 2);
v___x_949_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg___closed__0);
v___x_950_ = lean_box(0);
v___x_951_ = 0;
v___x_952_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_949_, v___x_946_, v_env_933_, v_asyncMode_948_, v___x_950_, v___x_951_);
v_sz_953_ = lean_array_size(v___x_952_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__0(v___x_943_, v_sz_953_, v___x_954_, v___x_952_);
v___x_956_ = l_Array_append___redArg(v___x_942_, v___x_955_);
lean_dec_ref(v___x_955_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(lean_object* v___x_957_, lean_object* v_inPackage_958_, lean_object* v_env_959_, lean_object* v_range_960_, lean_object* v_b_961_, lean_object* v_i_962_, lean_object* v_hs_963_, lean_object* v_hl_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___redArg(v___x_957_, v_inPackage_958_, v_env_959_, v_range_960_, v_b_961_, v_i_962_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1___boxed(lean_object* v___x_966_, lean_object* v_inPackage_967_, lean_object* v_env_968_, lean_object* v_range_969_, lean_object* v_b_970_, lean_object* v_i_971_, lean_object* v_hs_972_, lean_object* v_hl_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect_spec__1(v___x_966_, v_inPackage_967_, v_env_968_, v_range_969_, v_b_970_, v_i_971_, v_hs_972_, v_hl_973_);
lean_dec_ref(v_range_969_);
lean_dec_ref(v_env_968_);
lean_dec_ref(v___x_966_);
return v_res_974_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; size_t v___x_982_; size_t v___x_983_; 
v___x_980_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
lean_inc(v___x_980_);
v___x_981_ = l_Lean_NameSet_insert(v_b_978_, v___x_980_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_976_, v___x_982_);
v_i_976_ = v___x_983_;
v_b_978_ = v___x_981_;
goto _start;
}
else
{
return v_b_978_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_975_ = stack[0].m_obj;
size_t v_i_976_ = stack[1].m_num;
size_t v_stop_977_ = stack[2].m_num;
lean_object* v_b_978_ = stack[3].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_as_975_, v_i_976_, v_stop_977_, v_b_978_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3___boxed(lean_object* v_as_986_, lean_object* v_i_987_, lean_object* v_stop_988_, lean_object* v_b_989_){
_start:
{
size_t v_i_boxed_990_; size_t v_stop_boxed_991_; lean_object* v_res_992_; 
v_i_boxed_990_ = lean_unbox_usize(v_i_987_);
lean_dec(v_i_987_);
v_stop_boxed_991_ = lean_unbox_usize(v_stop_988_);
lean_dec(v_stop_988_);
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_as_986_, v_i_boxed_990_, v_stop_boxed_991_, v_b_989_);
lean_dec_ref(v_as_986_);
return v_res_992_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(lean_object* v___y_993_, lean_object* v_as_994_, size_t v_i_995_, size_t v_stop_996_, lean_object* v_b_997_){
_start:
{
lean_object* v___y_999_; uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_eq(v_i_995_, v_stop_996_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_uget_borrowed(v_as_994_, v_i_995_);
v___x_1005_ = l_Lean_NameSet_contains(v___y_993_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
lean_inc(v___x_1004_);
v___x_1006_ = lean_array_push(v_b_997_, v___x_1004_);
v___y_999_ = v___x_1006_;
goto v___jp_998_;
}
else
{
v___y_999_ = v_b_997_;
goto v___jp_998_;
}
}
else
{
return v_b_997_;
}
v___jp_998_:
{
size_t v___x_1000_; size_t v___x_1001_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_995_, v___x_1000_);
v_i_995_ = v___x_1001_;
v_b_997_ = v___y_999_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_993_ = stack[0].m_obj;
lean_object* v_as_994_ = stack[1].m_obj;
size_t v_i_995_ = stack[2].m_num;
size_t v_stop_996_ = stack[3].m_num;
lean_object* v_b_997_ = stack[4].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_993_, v_as_994_, v_i_995_, v_stop_996_, v_b_997_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1___boxed(lean_object* v___y_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_stop_1011_, lean_object* v_b_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; lean_object* v_res_1015_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1011_);
lean_dec(v_stop_1011_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_1008_, v_as_1009_, v_i_boxed_1013_, v_stop_boxed_1014_, v_b_1012_);
lean_dec_ref(v_as_1009_);
lean_dec(v___y_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
if (lean_obj_tag(v_a_1016_) == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = l_List_reverse___redArg(v_a_1017_);
return v___x_1018_;
}
else
{
lean_object* v_head_1019_; lean_object* v_tail_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
v_head_1019_ = lean_ctor_get(v_a_1016_, 0);
v_tail_1020_ = lean_ctor_get(v_a_1016_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1022_ = v_a_1016_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_tail_1020_);
lean_inc(v_head_1019_);
lean_dec(v_a_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = l_Lean_MessageData_ofName(v_head_1019_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_a_1017_);
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1017_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v_a_1016_ = v_tail_1020_;
v_a_1017_ = v___x_1026_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__0));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__2));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__4));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__6));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(lean_object* v_shouldCheck_1044_, lean_object* v_val_1045_, lean_object* v___x_1046_, lean_object* v___y_1047_, lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_a_1056_; uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec_ref(v_shouldCheck_1044_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_b_1051_);
return v___x_1061_;
}
else
{
lean_object* v_a_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1153_; 
v_a_1062_ = lean_array_uget(v_as_1048_, v_i_1050_);
v_fst_1063_ = lean_ctor_get(v_a_1062_, 0);
v_snd_1064_ = lean_ctor_get(v_a_1062_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_a_1062_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1066_ = v_a_1062_;
v_isShared_1067_ = v_isSharedCheck_1153_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_a_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1153_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___y_1082_; uint8_t v___y_1083_; lean_object* v_val_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_shouldCheck_1044_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v_snd_1064_);
v___x_1100_ = lean_apply_4(v_shouldCheck_1044_, v_snd_1064_, v___y_1052_, v___y_1053_, lean_box(0));
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; uint8_t v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1102_ == 0)
{
lean_del_object(v___x_1066_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
v_a_1056_ = v_b_1051_;
goto v___jp_1055_;
}
else
{
lean_object* v_imports_1103_; lean_object* v_check_1104_; lean_object* v___y_1106_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_imports_1103_ = lean_ctor_get(v_snd_1064_, 3);
v_check_1104_ = lean_ctor_get(v_snd_1064_, 7);
v___x_1135_ = lean_array_get_size(v_imports_1103_);
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__8));
v___x_1137_ = lean_nat_dec_lt(v___x_1099_, v___x_1135_);
if (v___x_1137_ == 0)
{
v___y_1106_ = v___x_1136_;
goto v___jp_1105_;
}
else
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_nat_dec_le(v___x_1135_, v___x_1135_);
if (v___x_1138_ == 0)
{
if (v___x_1137_ == 0)
{
v___y_1106_ = v___x_1136_;
goto v___jp_1105_;
}
else
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1135_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_1047_, v_imports_1103_, v___x_1139_, v___x_1140_, v___x_1136_);
v___y_1106_ = v___x_1141_;
goto v___jp_1105_;
}
}
else
{
size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = lean_usize_of_nat(v___x_1135_);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__1(v___y_1047_, v_imports_1103_, v___x_1142_, v___x_1143_, v___x_1136_);
v___y_1106_ = v___x_1144_;
goto v___jp_1105_;
}
}
v___jp_1105_:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_array_get_size(v___y_1106_);
v___x_1108_ = lean_nat_dec_eq(v___x_1107_, v___x_1099_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_del_object(v___x_1066_);
v___x_1109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__5);
v___x_1110_ = lean_array_to_list(v___y_1106_);
v___x_1111_ = lean_box(0);
v___x_1112_ = l_List_mapTR_loop___at___00Lean_Doc_DeferredCheck_run_spec__0(v___x_1110_, v___x_1111_);
v___x_1113_ = l_Lean_MessageData_ofList(v___x_1112_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1109_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__7);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_snd_1064_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_fst_1063_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_array_push(v_b_1051_, v___x_1118_);
v_a_1056_ = v___x_1119_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___y_1106_);
v___x_1120_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1104_);
v___x_1121_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_1045_, v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 1)
{
lean_dec(v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
goto v___jp_1068_;
}
else
{
lean_object* v_val_1122_; 
lean_del_object(v___x_1066_);
v_val_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_val_1090_ = v_val_1122_;
v___y_1091_ = v___y_1052_;
v___y_1092_ = v___y_1053_;
goto v___jp_1089_;
}
}
else
{
lean_object* v___x_1123_; 
lean_dec(v___x_1121_);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1046_, v___x_1120_);
lean_dec(v___x_1120_);
if (lean_obj_tag(v___x_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1066_);
v_val_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_getHandlerUnsafe(v_val_1124_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v_val_1090_ = v_a_1126_;
v___y_1091_ = v___y_1052_;
v___y_1092_ = v___y_1053_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec_ref(v_b_1051_);
lean_dec_ref(v_shouldCheck_1044_);
v_a_1127_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_dec(v___x_1123_);
goto v___jp_1068_;
}
}
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1066_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec_ref(v_b_1051_);
lean_dec_ref(v_shouldCheck_1044_);
v_a_1145_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1100_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1100_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
v___jp_1068_:
{
lean_object* v_check_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_check_1069_ = lean_ctor_get(v_snd_1064_, 7);
v___x_1070_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__1);
v___x_1071_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_check_1069_);
v___x_1072_ = l_Lean_MessageData_ofName(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1075_);
lean_ctor_set(v___x_1066_, 0, v_snd_1064_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_snd_1064_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_fst_1063_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_array_push(v_b_1051_, v___x_1078_);
v_a_1056_ = v___x_1079_;
goto v___jp_1055_;
}
}
v___jp_1081_:
{
if (v___y_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1084_ = l_Lean_Exception_toMessageData(v___y_1082_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_snd_1064_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_fst_1063_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_array_push(v_b_1051_, v___x_1086_);
v_a_1056_ = v___x_1087_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec_ref(v_b_1051_);
lean_dec_ref(v_shouldCheck_1044_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___y_1082_);
return v___x_1088_;
}
}
v___jp_1089_:
{
lean_object* v_check_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_check_1093_ = lean_ctor_get(v_snd_1064_, 7);
lean_inc(v_check_1093_);
v___x_1094_ = lean_apply_1(v_val_1090_, v_check_1093_);
lean_inc(v_snd_1064_);
v___x_1095_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_withScope___redArg(v_snd_1064_, v___x_1094_, v___y_1091_, v___y_1092_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
v_a_1056_ = v_b_1051_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1096_; uint8_t v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_Exception_isInterrupt(v_a_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
lean_inc(v_a_1096_);
v___x_1098_ = l_Lean_Exception_isRuntime(v_a_1096_);
v___y_1082_ = v_a_1096_;
v___y_1083_ = v___x_1098_;
goto v___jp_1081_;
}
else
{
v___y_1082_ = v_a_1096_;
v___y_1083_ = v___x_1097_;
goto v___jp_1081_;
}
}
}
}
}
v___jp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1050_, v___x_1057_);
v_i_1050_ = v___x_1058_;
v_b_1051_ = v_a_1056_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_shouldCheck_1044_ = stack[0].m_obj;
lean_object* v_val_1045_ = stack[1].m_obj;
lean_object* v___x_1046_ = stack[2].m_obj;
lean_object* v___y_1047_ = stack[3].m_obj;
lean_object* v_as_1048_ = stack[4].m_obj;
size_t v_sz_1049_ = stack[5].m_num;
size_t v_i_1050_ = stack[6].m_num;
lean_object* v_b_1051_ = stack[7].m_obj;
lean_object* v___y_1052_ = stack[8].m_obj;
lean_object* v___y_1053_ = stack[9].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1044_, v_val_1045_, v___x_1046_, v___y_1047_, v_as_1048_, v_sz_1049_, v_i_1050_, v_b_1051_, v___y_1052_, v___y_1053_);
stack->m_obj
 = v_res_1154_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2___boxed(lean_object* v_shouldCheck_1155_, lean_object* v_val_1156_, lean_object* v___x_1157_, lean_object* v___y_1158_, lean_object* v_as_1159_, lean_object* v_sz_1160_, lean_object* v_i_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1160_);
lean_dec(v_sz_1160_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1155_, v_val_1156_, v___x_1157_, v___y_1158_, v_as_1159_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v_as_1159_);
lean_dec(v___y_1158_);
lean_dec(v___x_1157_);
lean_dec(v_val_1156_);
return v_res_1168_;
}
}
lean_object* l_Lean_Doc_DeferredCheck_run(lean_object* v_inPackage_1171_, lean_object* v_shouldCheck_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_env_1178_; lean_object* v___x_1179_; lean_object* v_toEnvExtension_1180_; lean_object* v_asyncMode_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_moduleNames_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___y_1191_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1176_ = lean_box(1);
v___x_1177_ = lean_st_ref_get(v_a_1174_);
v_env_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_ref_n(v_env_1178_, 2);
lean_dec(v___x_1177_);
v___x_1179_ = l_Lean_Doc_DeferredCheck_handlerExt;
v_toEnvExtension_1180_ = lean_ctor_get(v___x_1179_, 0);
v_asyncMode_1181_ = lean_ctor_get(v_toEnvExtension_1180_, 2);
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1176_, v___x_1179_, v_env_1178_, v_asyncMode_1181_, v___x_1182_);
v___x_1184_ = l_Lean_Doc_DeferredCheck_builtinHandlers;
v___x_1185_ = lean_st_ref_get(v___x_1184_);
v___x_1186_ = l_Lean_Environment_header(v_env_1178_);
v_moduleNames_1187_ = lean_ctor_get(v___x_1186_, 4);
lean_inc_ref(v_moduleNames_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = l_Lean_NameSet_empty;
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_moduleNames_1187_);
v___x_1198_ = lean_nat_dec_lt(v___x_1189_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_moduleNames_1187_);
v___y_1191_ = v___x_1188_;
goto v___jp_1190_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_nat_dec_le(v___x_1197_, v___x_1197_);
if (v___x_1199_ == 0)
{
if (v___x_1198_ == 0)
{
lean_dec_ref(v_moduleNames_1187_);
v___y_1191_ = v___x_1188_;
goto v___jp_1190_;
}
else
{
size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = lean_usize_of_nat(v___x_1197_);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_moduleNames_1187_, v___x_1200_, v___x_1201_, v___x_1188_);
lean_dec_ref(v_moduleNames_1187_);
v___y_1191_ = v___x_1202_;
goto v___jp_1190_;
}
}
else
{
size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = lean_usize_of_nat(v___x_1197_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_DeferredCheck_run_spec__3(v_moduleNames_1187_, v___x_1203_, v___x_1204_, v___x_1188_);
lean_dec_ref(v_moduleNames_1187_);
v___y_1191_ = v___x_1205_;
goto v___jp_1190_;
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; size_t v_sz_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1192_ = ((lean_object*)(l_Lean_Doc_DeferredCheck_run___closed__0));
v___x_1193_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_DeferredCheck_collect(v_env_1178_, v_inPackage_1171_);
v_sz_1194_ = lean_array_size(v___x_1193_);
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_DeferredCheck_run_spec__2(v_shouldCheck_1172_, v___x_1185_, v___x_1183_, v___y_1191_, v___x_1193_, v_sz_1194_, v___x_1195_, v___x_1192_, v_a_1173_, v_a_1174_);
lean_dec_ref(v___x_1193_);
lean_dec(v___y_1191_);
lean_dec(v___x_1183_);
lean_dec(v___x_1185_);
return v___x_1196_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_DeferredCheck_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_inPackage_1171_ = stack[0].m_obj;
lean_object* v_shouldCheck_1172_ = stack[1].m_obj;
lean_object* v_a_1173_ = stack[2].m_obj;
lean_object* v_a_1174_ = stack[3].m_obj;
lean_object* v_res_1206_;
v_res_1206_ = l_Lean_Doc_DeferredCheck_run(v_inPackage_1171_, v_shouldCheck_1172_, v_a_1173_, v_a_1174_);
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheck_run___boxed(lean_object* v_inPackage_1207_, lean_object* v_shouldCheck_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Doc_DeferredCheck_run(v_inPackage_1207_, v_shouldCheck_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1212_;
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
