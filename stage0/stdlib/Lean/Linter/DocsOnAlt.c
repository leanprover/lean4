// Lean compiler output
// Module: Lean.Linter.DocsOnAlt
// Imports: import Lean.Parser.Syntax public import Lean.Data.Options import Lean.Elab.Command import Lean.Linter.Init import Lean.Elab.InfoTree.Util
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "docsOnAlt"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 206, 61, 199, 208, 244, 88, 253)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(130, 179, 177, 23, 55, 162, 149, 215)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "enable the 'documentation on tactic alternatives' linter"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 227, 207, 47, 218, 2, 231, 228)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(45, 59, 71, 172, 106, 21, 26, 4)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_tactic_docsOnAlt;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt___boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Documentation for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` is ignored because it is a tactic alternative."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Documentation is ignored on a tactic alternative."};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value;
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value;
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value;
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__2_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__1_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__0_value)} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__5_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__6_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocsOnAlt"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__7_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value),LEAN_SCALAR_PTR_LITERAL(245, 34, 188, 50, 6, 154, 66, 170)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(224, 190, 97, 116, 249, 86, 187, 6)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__10_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 161, 36, 214, 111, 223, 124, 109)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__11_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(67, 195, 153, 241, 76, 214, 14, 4)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__12_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__8_value),LEAN_SCALAR_PTR_LITERAL(94, 165, 12, 255, 208, 202, 70, 49)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__13_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(178, 6, 92, 10, 248, 88, 218, 68)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__3_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__14_value)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value;
LEAN_EXPORT const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(lean_object* v_o_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = l_Lean_Linter_linter_tactic_docsOnAlt;
v___x_64_ = l_Lean_Linter_getLinterValue(v___x_63_, v_o_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt___boxed(lean_object* v_o_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(v_o_65_);
lean_dec_ref(v_o_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr(lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__3));
v___x_78_ = l_Lean_Syntax_isOfKind(v_a_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___boxed(lean_object* v_a_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr(v_a_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0(lean_object* v_x_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l_Lean_Syntax_getKind(v_x_89_);
v___x_91_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__2));
v___x_92_ = lean_name_eq(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0(v_x_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1(lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Lean_Syntax_getKind(v_x_102_);
v___x_104_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___closed__1));
v___x_105_ = lean_name_eq(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__1(v_x_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; uint8_t v___x_114_; 
v_head_112_ = lean_ctor_get(v_x_110_, 0);
v_tail_113_ = lean_ctor_get(v_x_110_, 1);
v___x_114_ = lean_name_eq(v_a_109_, v_head_112_);
if (v___x_114_ == 0)
{
v_x_110_ = v_tail_113_;
goto _start;
}
else
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0___boxed(lean_object* v_a_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v_a_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_a_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_Syntax_getKind(v_x_138_);
v___x_140_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5));
v___x_141_ = l_List_elem___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(v_x_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg(lean_object* v_o_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_env_150_; lean_object* v___x_151_; lean_object* v_toEnvExtension_152_; lean_object* v_asyncMode_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v_merged_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v___x_148_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_149_ = lean_st_ref_get(v___y_146_);
v_env_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc_ref(v_env_150_);
lean_dec(v___x_149_);
v___x_151_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_152_ = lean_ctor_get(v___x_151_, 0);
v_asyncMode_153_ = lean_ctor_get(v_toEnvExtension_152_, 2);
v___x_154_ = lean_box(0);
v___x_155_ = 0;
v___x_156_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_148_, v___x_151_, v_env_150_, v_asyncMode_153_, v___x_154_, v___x_155_);
v_merged_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v___x_156_, 1);
lean_dec(v_unused_166_);
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_merged_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_merged_157_);
lean_ctor_set(v___x_159_, 0, v_o_145_);
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_o_145_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_merged_157_);
v___x_162_ = v_reuseFailAlloc_164_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg___boxed(lean_object* v_o_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg(v_o_167_, v___y_168_);
lean_dec(v___y_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_scopes_176_; lean_object* v___x_177_; lean_object* v_opts_178_; lean_object* v___x_179_; 
v___x_174_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_175_ = lean_st_ref_get(v___y_172_);
v_scopes_176_ = lean_ctor_get(v___x_175_, 2);
lean_inc(v_scopes_176_);
lean_dec(v___x_175_);
v___x_177_ = l_List_head_x21___redArg(v___x_174_, v_scopes_176_);
lean_dec(v_scopes_176_);
v_opts_178_ = lean_ctor_get(v___x_177_, 1);
lean_inc_ref(v_opts_178_);
lean_dec(v___x_177_);
v___x_179_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg(v_opts_178_, v___y_172_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___boxed(lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_183_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_instMonadEIO___redArg();
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg(lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_toApplicative_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_224_; 
v___x_191_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__0);
v___x_192_ = l_StateRefT_x27_instMonad___redArg(v___x_191_);
v_toApplicative_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v___x_192_, 1);
lean_dec(v_unused_225_);
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_224_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_toApplicative_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_224_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_toFunctor_197_; lean_object* v_toSeq_198_; lean_object* v_toSeqLeft_199_; lean_object* v_toSeqRight_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_222_; 
v_toFunctor_197_ = lean_ctor_get(v_toApplicative_193_, 0);
v_toSeq_198_ = lean_ctor_get(v_toApplicative_193_, 2);
v_toSeqLeft_199_ = lean_ctor_get(v_toApplicative_193_, 3);
v_toSeqRight_200_ = lean_ctor_get(v_toApplicative_193_, 4);
v_isSharedCheck_222_ = !lean_is_exclusive(v_toApplicative_193_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_toApplicative_193_, 1);
lean_dec(v_unused_223_);
v___x_202_ = v_toApplicative_193_;
v_isShared_203_ = v_isSharedCheck_222_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_toSeqRight_200_);
lean_inc(v_toSeqLeft_199_);
lean_inc(v_toSeq_198_);
lean_inc(v_toFunctor_197_);
lean_dec(v_toApplicative_193_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_222_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_213_; 
v___f_204_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__1));
v___f_205_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___closed__2));
lean_inc_ref(v_toFunctor_197_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_206_, 0, v_toFunctor_197_);
v___f_207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_207_, 0, v_toFunctor_197_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___f_206_);
lean_ctor_set(v___x_208_, 1, v___f_207_);
v___f_209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_209_, 0, v_toSeqRight_200_);
v___f_210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_210_, 0, v_toSeqLeft_199_);
v___f_211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_211_, 0, v_toSeq_198_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 4, v___f_209_);
lean_ctor_set(v___x_202_, 3, v___f_210_);
lean_ctor_set(v___x_202_, 2, v___f_211_);
lean_ctor_set(v___x_202_, 1, v___f_204_);
lean_ctor_set(v___x_202_, 0, v___x_208_);
v___x_213_ = v___x_202_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___f_204_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v___f_211_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v___f_210_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v___f_209_);
v___x_213_ = v_reuseFailAlloc_221_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___f_205_);
lean_ctor_set(v___x_195_, 0, v___x_213_);
v___x_215_ = v___x_195_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___f_205_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_6588__overap_218_; lean_object* v___x_219_; 
v___x_216_ = lean_box(0);
v___x_217_ = l_instInhabitedOfMonad___redArg(v___x_215_, v___x_216_);
v___x_6588__overap_218_ = lean_panic_fn_borrowed(v___x_217_, v_msg_187_);
lean_dec(v___x_217_);
lean_inc(v___y_189_);
lean_inc_ref(v___y_188_);
v___x_219_ = lean_apply_3(v___x_6588__overap_218_, v___y_188_, v___y_189_, lean_box(0));
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg(v_msg_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_230_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_234_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__2));
v___x_235_ = lean_unsigned_to_nat(21u);
v___x_236_ = lean_unsigned_to_nat(65u);
v___x_237_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__1));
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__0));
v___x_239_ = l_mkPanicMessageWithDecl(v___x_238_, v___x_237_, v___x_236_, v___x_235_, v___x_234_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(lean_object* v_preNode_240_, lean_object* v_postNode_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
switch(lean_obj_tag(v_x_243_))
{
case 0:
{
lean_object* v_i_247_; lean_object* v_t_248_; lean_object* v___x_249_; 
v_i_247_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref(v_i_247_);
v_t_248_ = lean_ctor_get(v_x_243_, 1);
lean_inc_ref(v_t_248_);
lean_dec_ref_known(v_x_243_, 2);
v___x_249_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_247_, v_x_242_);
v_x_242_ = v___x_249_;
v_x_243_ = v_t_248_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v___x_251_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___closed__3);
v___x_252_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg(v___x_251_, v___y_244_, v___y_245_);
return v___x_252_;
}
else
{
lean_object* v_i_253_; lean_object* v_children_254_; lean_object* v_val_255_; lean_object* v___x_256_; 
v_i_253_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref_n(v_i_253_, 2);
v_children_254_ = lean_ctor_get(v_x_243_, 1);
lean_inc_ref_n(v_children_254_, 2);
lean_dec_ref_known(v_x_243_, 2);
v_val_255_ = lean_ctor_get(v_x_242_, 0);
lean_inc_n(v_val_255_, 2);
lean_inc_ref(v_preNode_240_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_256_ = lean_apply_6(v_preNode_240_, v_val_255_, v_i_253_, v_children_254_, v___y_244_, v___y_245_, lean_box(0));
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; uint8_t v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = lean_unbox(v_a_257_);
lean_dec(v_a_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_preNode_240_);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_x_242_, 0);
lean_dec(v_unused_284_);
v___x_260_ = v_x_242_;
v_isShared_261_ = v_isSharedCheck_283_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_x_242_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_283_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box(0);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_263_ = lean_apply_7(v_postNode_241_, v_val_255_, v_i_253_, v_children_254_, v___x_262_, v___y_244_, v___y_245_, lean_box(0));
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_274_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_274_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_a_264_);
v___x_269_ = v___x_260_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_271_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
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
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_del_object(v___x_260_);
v_a_275_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_263_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_263_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = l_Lean_Elab_Info_updateContext_x3f(v_x_242_, v_i_253_);
v___x_286_ = l_Lean_PersistentArray_toList___redArg(v_children_254_);
v___x_287_ = lean_box(0);
lean_inc_ref(v_postNode_241_);
v___x_288_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg(v_preNode_240_, v_postNode_241_, v___x_285_, v___x_286_, v___x_287_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_290_ = lean_apply_7(v_postNode_241_, v_val_255_, v_i_253_, v_children_254_, v_a_289_, v___y_244_, v___y_245_, lean_box(0));
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_a_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_290_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_val_255_);
lean_dec_ref(v_children_254_);
lean_dec_ref(v_i_253_);
lean_dec_ref(v_postNode_241_);
v_a_308_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_288_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_288_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_val_255_);
lean_dec_ref(v_children_254_);
lean_dec_ref(v_i_253_);
lean_dec_ref_known(v_x_242_, 1);
lean_dec_ref(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v_a_316_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_256_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_256_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
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
}
default: 
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_x_242_);
lean_dec_ref(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_x_243_, 0);
lean_dec(v_unused_332_);
v___x_325_ = v_x_243_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_dec(v_x_243_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_box(0);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 0);
lean_ctor_set(v___x_325_, 0, v___x_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg(lean_object* v_preNode_333_, lean_object* v_postNode_334_, lean_object* v___x_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v___x_335_);
lean_dec_ref(v_postNode_334_);
lean_dec_ref(v_preNode_333_);
v___x_341_ = l_List_reverse___redArg(v_x_337_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
else
{
lean_object* v_head_343_; lean_object* v_tail_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_362_; 
v_head_343_ = lean_ctor_get(v_x_336_, 0);
v_tail_344_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_362_ == 0)
{
v___x_346_ = v_x_336_;
v_isShared_347_ = v_isSharedCheck_362_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_tail_344_);
lean_inc(v_head_343_);
lean_dec(v_x_336_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_362_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; 
lean_inc(v___x_335_);
lean_inc_ref(v_postNode_334_);
lean_inc_ref(v_preNode_333_);
v___x_348_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(v_preNode_333_, v_postNode_334_, v___x_335_, v_head_343_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_x_337_);
lean_ctor_set(v___x_346_, 0, v_a_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_x_337_);
v___x_351_ = v_reuseFailAlloc_353_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
v_x_336_ = v_tail_344_;
v_x_337_ = v___x_351_;
goto _start;
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_del_object(v___x_346_);
lean_dec(v_tail_344_);
lean_dec(v_x_337_);
lean_dec(v___x_335_);
lean_dec_ref(v_postNode_334_);
lean_dec_ref(v_preNode_333_);
v_a_354_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_348_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_348_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_preNode_363_, lean_object* v_postNode_364_, lean_object* v___x_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg(v_preNode_363_, v_postNode_364_, v___x_365_, v_x_366_, v_x_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg___boxed(lean_object* v_preNode_372_, lean_object* v_postNode_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(v_preNode_372_, v_postNode_373_, v_x_374_, v_x_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(lean_object* v_postNode_380_, lean_object* v_ci_381_, lean_object* v_i_382_, lean_object* v_cs_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
v___x_388_ = lean_apply_6(v_postNode_380_, v_ci_381_, v_i_382_, v_cs_383_, v___y_385_, v___y_386_, lean_box(0));
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed(lean_object* v_postNode_389_, lean_object* v_ci_390_, lean_object* v_i_391_, lean_object* v_cs_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(v_postNode_389_, v_ci_390_, v_i_391_, v_cs_392_, v_x_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v_x_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(lean_object* v_preNode_398_, lean_object* v_postNode_399_, lean_object* v_ctx_x3f_400_, lean_object* v_t_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_405_, 0, v_postNode_399_);
v___x_406_ = lean_box(0);
v___x_407_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(v_preNode_398_, v___f_405_, v_ctx_x3f_400_, v_t_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_407_, 0);
lean_dec(v_unused_415_);
v___x_409_ = v___x_407_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_dec(v___x_407_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_406_);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_406_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_407_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_407_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___boxed(lean_object* v_preNode_424_, lean_object* v_postNode_425_, lean_object* v_ctx_x3f_426_, lean_object* v_t_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v_preNode_424_, v_postNode_425_, v_ctx_x3f_426_, v_t_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5(lean_object* v_a_432_, lean_object* v_as_433_, size_t v_i_434_, size_t v_stop_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_434_, v_stop_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_uget_borrowed(v_as_433_, v_i_434_);
v___x_438_ = l_Lean_Syntax_structEq(v_a_432_, v___x_437_);
if (v___x_438_ == 0)
{
size_t v___x_439_; size_t v___x_440_; 
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_434_, v___x_439_);
v_i_434_ = v___x_440_;
goto _start;
}
else
{
return v___x_438_;
}
}
else
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5___boxed(lean_object* v_a_443_, lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_stop_446_){
_start:
{
size_t v_i_boxed_447_; size_t v_stop_boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_i_boxed_447_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_stop_boxed_448_ = lean_unbox_usize(v_stop_446_);
lean_dec(v_stop_446_);
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5(v_a_443_, v_as_444_, v_i_boxed_447_, v_stop_boxed_448_);
lean_dec_ref(v_as_444_);
lean_dec(v_a_443_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(lean_object* v_as_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_array_get_size(v_as_451_);
v___x_455_ = lean_nat_dec_lt(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = ((size_t)0ULL);
v___x_457_ = lean_usize_of_nat(v___x_454_);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__5(v_a_452_, v_as_451_, v___x_456_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___boxed(lean_object* v_as_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v_as_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_as_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9(lean_object* v_opts_463_, lean_object* v_opt_464_){
_start:
{
lean_object* v_name_465_; lean_object* v_defValue_466_; lean_object* v_map_467_; lean_object* v___x_468_; 
v_name_465_ = lean_ctor_get(v_opt_464_, 0);
v_defValue_466_ = lean_ctor_get(v_opt_464_, 1);
v_map_467_ = lean_ctor_get(v_opts_463_, 0);
v___x_468_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_467_, v_name_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = lean_unbox(v_defValue_466_);
return v___x_469_;
}
else
{
lean_object* v_val_470_; 
v_val_470_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_468_, 1);
if (lean_obj_tag(v_val_470_) == 1)
{
uint8_t v_v_471_; 
v_v_471_ = lean_ctor_get_uint8(v_val_470_, 0);
lean_dec_ref_known(v_val_470_, 0);
return v_v_471_;
}
else
{
uint8_t v___x_472_; 
lean_dec(v_val_470_);
v___x_472_ = lean_unbox(v_defValue_466_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9___boxed(lean_object* v_opts_473_, lean_object* v_opt_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9(v_opts_473_, v_opt_474_);
lean_dec_ref(v_opt_474_);
lean_dec_ref(v_opts_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_477_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__0);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
lean_ctor_set(v___x_482_, 3, v___x_481_);
lean_ctor_set(v___x_482_, 4, v___x_480_);
lean_ctor_set(v___x_482_, 5, v___x_480_);
lean_ctor_set(v___x_482_, 6, v___x_480_);
lean_ctor_set(v___x_482_, 7, v___x_480_);
lean_ctor_set(v___x_482_, 8, v___x_480_);
lean_ctor_set(v___x_482_, 9, v___x_480_);
lean_ctor_set(v___x_482_, 10, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(32u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_486_ = ((size_t)5ULL);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_unsigned_to_nat(32u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
v___x_490_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__3);
v___x_491_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_489_);
lean_ctor_set(v___x_491_, 2, v___x_487_);
lean_ctor_set(v___x_491_, 3, v___x_487_);
lean_ctor_set_usize(v___x_491_, 4, v___x_486_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_box(1);
v___x_493_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__4);
v___x_494_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__1);
v___x_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg(lean_object* v_msgData_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v_env_500_; uint8_t v___x_501_; lean_object* v_env_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_scopes_505_; lean_object* v___x_506_; lean_object* v_opts_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_499_ = lean_st_ref_get(v___y_497_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_env_500_);
lean_dec(v___x_499_);
v___x_501_ = 0;
v_env_502_ = l_Lean_Environment_setRecordingDeps(v_env_500_, v___x_501_);
v___x_503_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_504_ = lean_st_ref_get(v___y_497_);
v_scopes_505_ = lean_ctor_get(v___x_504_, 2);
lean_inc(v_scopes_505_);
lean_dec(v___x_504_);
v___x_506_ = l_List_head_x21___redArg(v___x_503_, v_scopes_505_);
lean_dec(v_scopes_505_);
v_opts_507_ = lean_ctor_get(v___x_506_, 1);
lean_inc_ref(v_opts_507_);
lean_dec(v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__2);
v___x_509_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___closed__5);
v___x_510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_510_, 0, v_env_502_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
lean_ctor_set(v___x_510_, 3, v_opts_507_);
v___x_511_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_msgData_496_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_msgData_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg(v_msgData_513_, v___y_514_);
lean_dec(v___y_514_);
return v_res_516_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0(uint8_t v_suppressElabErrors_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 1)
{
lean_object* v_pre_520_; 
v_pre_520_ = lean_ctor_get(v_x_519_, 0);
if (lean_obj_tag(v_pre_520_) == 0)
{
lean_object* v_str_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_str_521_ = lean_ctor_get(v_x_519_, 1);
v___x_522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___closed__0));
v___x_523_ = lean_string_dec_eq(v_str_521_, v___x_522_);
if (v___x_523_ == 0)
{
return v___x_523_;
}
else
{
return v_suppressElabErrors_518_;
}
}
else
{
uint8_t v___x_524_; 
v___x_524_ = 0;
return v___x_524_;
}
}
else
{
uint8_t v___x_525_; 
v___x_525_ = 0;
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_526_, lean_object* v_x_527_){
_start:
{
uint8_t v_suppressElabErrors_boxed_528_; uint8_t v_res_529_; lean_object* v_r_530_; 
v_suppressElabErrors_boxed_528_ = lean_unbox(v_suppressElabErrors_526_);
v_res_529_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0(v_suppressElabErrors_boxed_528_, v_x_527_);
lean_dec(v_x_527_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4(lean_object* v_ref_532_, lean_object* v_msgData_533_, uint8_t v_severity_534_, uint8_t v_isSilent_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_605_; uint8_t v___y_606_; uint8_t v___y_607_; lean_object* v___y_608_; uint8_t v___y_631_; lean_object* v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; uint8_t v___y_638_; uint8_t v___y_639_; uint8_t v___x_654_; uint8_t v___y_656_; uint8_t v___x_666_; 
v___x_654_ = 2;
v___x_666_ = l_Lean_instBEqMessageSeverity_beq(v_severity_534_, v___x_654_);
if (v___x_666_ == 0)
{
v___y_656_ = v___x_666_;
goto v___jp_655_;
}
else
{
uint8_t v___x_667_; 
lean_inc_ref(v_msgData_533_);
v___x_667_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_533_);
if (v___x_667_ == 0)
{
v___y_656_ = v___x_667_;
goto v___jp_655_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec_ref(v_msgData_533_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
v___jp_539_:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Elab_Command_getScope___redArg(v___y_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_currNamespace_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v_currNamespace_550_ = lean_ctor_get(v_a_549_, 2);
lean_inc(v_currNamespace_550_);
lean_dec(v_a_549_);
v___x_551_ = l_Lean_Elab_Command_getScope___redArg(v___y_547_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_587_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_587_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_587_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_587_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_openDecls_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_env_561_; lean_object* v_messages_562_; lean_object* v_scopes_563_; lean_object* v_usedQuotCtxts_564_; lean_object* v_nextMacroScope_565_; lean_object* v_maxRecDepth_566_; lean_object* v_ngen_567_; lean_object* v_auxDeclNGen_568_; lean_object* v_infoState_569_; lean_object* v_traceState_570_; lean_object* v_snapshotTasks_571_; lean_object* v_prevLinterStates_572_; lean_object* v_codeQualityEntryTasks_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_586_; 
v_openDecls_556_ = lean_ctor_get(v_a_552_, 3);
lean_inc(v_openDecls_556_);
lean_dec(v_a_552_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_currNamespace_550_);
lean_ctor_set(v___x_557_, 1, v_openDecls_556_);
v___x_558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___y_540_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_544_);
v___x_559_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_559_, 0, v___y_544_);
lean_ctor_set(v___x_559_, 1, v___y_541_);
lean_ctor_set(v___x_559_, 2, v___y_543_);
lean_ctor_set(v___x_559_, 3, v___y_546_);
lean_ctor_set(v___x_559_, 4, v___x_558_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5, v___y_542_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5 + 1, v___y_545_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5 + 2, v_isSilent_535_);
v___x_560_ = lean_st_ref_take(v___y_547_);
v_env_561_ = lean_ctor_get(v___x_560_, 0);
v_messages_562_ = lean_ctor_get(v___x_560_, 1);
v_scopes_563_ = lean_ctor_get(v___x_560_, 2);
v_usedQuotCtxts_564_ = lean_ctor_get(v___x_560_, 3);
v_nextMacroScope_565_ = lean_ctor_get(v___x_560_, 4);
v_maxRecDepth_566_ = lean_ctor_get(v___x_560_, 5);
v_ngen_567_ = lean_ctor_get(v___x_560_, 6);
v_auxDeclNGen_568_ = lean_ctor_get(v___x_560_, 7);
v_infoState_569_ = lean_ctor_get(v___x_560_, 8);
v_traceState_570_ = lean_ctor_get(v___x_560_, 9);
v_snapshotTasks_571_ = lean_ctor_get(v___x_560_, 10);
v_prevLinterStates_572_ = lean_ctor_get(v___x_560_, 11);
v_codeQualityEntryTasks_573_ = lean_ctor_get(v___x_560_, 12);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_586_ == 0)
{
v___x_575_ = v___x_560_;
v_isShared_576_ = v_isSharedCheck_586_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_codeQualityEntryTasks_573_);
lean_inc(v_prevLinterStates_572_);
lean_inc(v_snapshotTasks_571_);
lean_inc(v_traceState_570_);
lean_inc(v_infoState_569_);
lean_inc(v_auxDeclNGen_568_);
lean_inc(v_ngen_567_);
lean_inc(v_maxRecDepth_566_);
lean_inc(v_nextMacroScope_565_);
lean_inc(v_usedQuotCtxts_564_);
lean_inc(v_scopes_563_);
lean_inc(v_messages_562_);
lean_inc(v_env_561_);
lean_dec(v___x_560_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_586_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_box(0);
v___x_578_ = l_Lean_MessageLog_add(v___x_559_, v_messages_562_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 1, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_env_561_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_scopes_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_usedQuotCtxts_564_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_nextMacroScope_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v_maxRecDepth_566_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_ngen_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_auxDeclNGen_568_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_infoState_569_);
lean_ctor_set(v_reuseFailAlloc_585_, 9, v_traceState_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 10, v_snapshotTasks_571_);
lean_ctor_set(v_reuseFailAlloc_585_, 11, v_prevLinterStates_572_);
lean_ctor_set(v_reuseFailAlloc_585_, 12, v_codeQualityEntryTasks_573_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_st_ref_put(v___y_547_, v___x_580_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_577_);
v___x_583_ = v___x_554_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_577_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_currNamespace_550_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_541_);
lean_dec_ref(v___y_540_);
v_a_588_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_551_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_551_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v___y_543_);
lean_dec_ref(v___y_541_);
lean_dec_ref(v___y_540_);
v_a_596_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_548_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_548_);
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
v___jp_604_:
{
lean_object* v_fileName_609_; lean_object* v_fileMap_610_; uint8_t v_suppressElabErrors_611_; lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_629_; 
v_fileName_609_ = lean_ctor_get(v___y_536_, 0);
v_fileMap_610_ = lean_ctor_get(v___y_536_, 1);
v_suppressElabErrors_611_ = lean_ctor_get_uint8(v___y_536_, sizeof(void*)*10);
v___x_612_ = lean_box(v_suppressElabErrors_611_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_613_, 0, v___x_612_);
v___x_614_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_533_);
v___x_615_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg(v___x_614_, v___y_537_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_629_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc_ref_n(v_fileMap_610_, 2);
v___x_620_ = l_Lean_FileMap_toPosition(v_fileMap_610_, v___y_605_);
lean_dec(v___y_605_);
v___x_621_ = l_Lean_FileMap_toPosition(v_fileMap_610_, v___y_608_);
lean_dec(v___y_608_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___closed__0));
if (v_suppressElabErrors_611_ == 0)
{
lean_del_object(v___x_618_);
lean_dec_ref(v___f_613_);
v___y_540_ = v_a_616_;
v___y_541_ = v___x_620_;
v___y_542_ = v___y_606_;
v___y_543_ = v___x_622_;
v___y_544_ = v_fileName_609_;
v___y_545_ = v___y_607_;
v___y_546_ = v___x_623_;
v___y_547_ = v___y_537_;
goto v___jp_539_;
}
else
{
uint8_t v___x_624_; 
lean_inc(v_a_616_);
v___x_624_ = l_Lean_MessageData_hasTag(v___f_613_, v_a_616_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_dec_ref_known(v___x_622_, 1);
lean_dec_ref(v___x_620_);
lean_dec(v_a_616_);
v___x_625_ = lean_box(0);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_625_);
v___x_627_ = v___x_618_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_del_object(v___x_618_);
v___y_540_ = v_a_616_;
v___y_541_ = v___x_620_;
v___y_542_ = v___y_606_;
v___y_543_ = v___x_622_;
v___y_544_ = v_fileName_609_;
v___y_545_ = v___y_607_;
v___y_546_ = v___x_623_;
v___y_547_ = v___y_537_;
goto v___jp_539_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Syntax_getTailPos_x3f(v___y_632_, v___y_631_);
lean_dec(v___y_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_inc(v___y_634_);
v___y_605_ = v___y_634_;
v___y_606_ = v___y_631_;
v___y_607_ = v___y_633_;
v___y_608_ = v___y_634_;
goto v___jp_604_;
}
else
{
lean_object* v_val_636_; 
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_635_, 1);
v___y_605_ = v___y_634_;
v___y_606_ = v___y_631_;
v___y_607_ = v___y_633_;
v___y_608_ = v_val_636_;
goto v___jp_604_;
}
}
v___jp_637_:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Elab_Command_getRef___redArg(v___y_536_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_ref_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v_ref_642_ = l_Lean_replaceRef(v_ref_532_, v_a_641_);
lean_dec(v_a_641_);
v___x_643_ = l_Lean_Syntax_getPos_x3f(v_ref_642_, v___y_638_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___y_631_ = v___y_638_;
v___y_632_ = v_ref_642_;
v___y_633_ = v___y_639_;
v___y_634_ = v___x_644_;
goto v___jp_630_;
}
else
{
lean_object* v_val_645_; 
v_val_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_645_);
lean_dec_ref_known(v___x_643_, 1);
v___y_631_ = v___y_638_;
v___y_632_ = v_ref_642_;
v___y_633_ = v___y_639_;
v___y_634_ = v_val_645_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_msgData_533_);
v_a_646_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_640_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_scopes_659_; lean_object* v___x_660_; lean_object* v_opts_661_; uint8_t v___x_662_; uint8_t v___x_663_; 
v___x_657_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_658_ = lean_st_ref_get(v___y_537_);
v_scopes_659_ = lean_ctor_get(v___x_658_, 2);
lean_inc(v_scopes_659_);
lean_dec(v___x_658_);
v___x_660_ = l_List_head_x21___redArg(v___x_657_, v_scopes_659_);
lean_dec(v_scopes_659_);
v_opts_661_ = lean_ctor_get(v___x_660_, 1);
lean_inc_ref(v_opts_661_);
lean_dec(v___x_660_);
v___x_662_ = 1;
v___x_663_ = l_Lean_instBEqMessageSeverity_beq(v_severity_534_, v___x_662_);
if (v___x_663_ == 0)
{
lean_dec_ref(v_opts_661_);
v___y_638_ = v___y_656_;
v___y_639_ = v_severity_534_;
goto v___jp_637_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = l_Lean_warningAsError;
v___x_665_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__9(v_opts_661_, v___x_664_);
lean_dec_ref(v_opts_661_);
if (v___x_665_ == 0)
{
v___y_638_ = v___y_656_;
v___y_639_ = v_severity_534_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___y_656_;
v___y_639_ = v___x_654_;
goto v___jp_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_670_, lean_object* v_msgData_671_, lean_object* v_severity_672_, lean_object* v_isSilent_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v_severity_boxed_677_; uint8_t v_isSilent_boxed_678_; lean_object* v_res_679_; 
v_severity_boxed_677_ = lean_unbox(v_severity_672_);
v_isSilent_boxed_678_ = lean_unbox(v_isSilent_673_);
v_res_679_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4(v_ref_670_, v_msgData_671_, v_severity_boxed_677_, v_isSilent_boxed_678_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v_ref_670_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3(lean_object* v_ref_680_, lean_object* v_msgData_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = 1;
v___x_686_ = 0;
v___x_687_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4(v_ref_680_, v_msgData_681_, v___x_685_, v___x_686_, v___y_682_, v___y_683_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3___boxed(lean_object* v_ref_688_, lean_object* v_msgData_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3(v_ref_688_, v_msgData_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v_ref_688_);
return v_res_693_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__0));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__2));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(lean_object* v_linterOption_700_, lean_object* v_stx_701_, lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_name_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_724_; 
v_name_706_ = lean_ctor_get(v_linterOption_700_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_linterOption_700_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_linterOption_700_, 1);
lean_dec(v_unused_725_);
v___x_708_ = v_linterOption_700_;
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_name_706_);
lean_dec(v_linterOption_700_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__1);
lean_inc(v_name_706_);
v___x_711_ = l_Lean_MessageData_ofName(v_name_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 7);
lean_ctor_set(v___x_708_, 1, v___x_711_);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_723_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_disable_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_714_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___closed__3);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v_disable_716_ = l_Lean_MessageData_note(v___x_715_);
v___x_717_ = l_Lean_Linter_linterMessageTag;
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v_msg_702_);
lean_ctor_set(v___x_718_, 1, v_disable_716_);
v___x_719_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_720_, 0, v_name_706_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_inc(v_stx_701_);
v___x_721_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_721_, 0, v_stx_701_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3(v_stx_701_, v___x_721_, v___y_703_, v___y_704_);
lean_dec(v_stx_701_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___boxed(lean_object* v_linterOption_726_, lean_object* v_stx_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v_linterOption_726_, v_stx_727_, v_msg_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__2));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1(lean_object* v___x_739_, uint8_t v___x_740_, lean_object* v_ci_741_, lean_object* v_info_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
if (lean_obj_tag(v_info_742_) == 1)
{
lean_object* v_i_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_808_; 
v_i_747_ = lean_ctor_get(v_info_742_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_info_742_);
if (v_isSharedCheck_808_ == 0)
{
v___x_749_ = v_info_742_;
v_isShared_750_ = v_isSharedCheck_808_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_i_747_);
lean_dec(v_info_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_808_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_toElabInfo_751_; lean_object* v_expr_752_; lean_object* v_stx_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_806_; 
v_toElabInfo_751_ = lean_ctor_get(v_i_747_, 0);
lean_inc_ref(v_toElabInfo_751_);
v_expr_752_ = lean_ctor_get(v_i_747_, 3);
lean_inc_ref(v_expr_752_);
lean_dec_ref(v_i_747_);
v_stx_753_ = lean_ctor_get(v_toElabInfo_751_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_toElabInfo_751_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_toElabInfo_751_, 0);
lean_dec(v_unused_807_);
v___x_755_ = v_toElabInfo_751_;
v_isShared_756_ = v_isSharedCheck_806_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_stx_753_);
lean_dec(v_toElabInfo_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_806_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
uint8_t v___x_757_; 
v___x_757_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v___x_739_, v_stx_753_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_del_object(v___x_755_);
lean_dec(v_stx_753_);
lean_dec_ref(v_expr_752_);
lean_dec_ref(v_ci_741_);
v___x_758_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 0);
lean_ctor_set(v___x_749_, 0, v___x_758_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
if (lean_obj_tag(v_expr_752_) == 4)
{
lean_object* v_toCommandContextInfo_762_; lean_object* v_declName_763_; lean_object* v_env_764_; lean_object* v___x_765_; 
v_toCommandContextInfo_762_ = lean_ctor_get(v_ci_741_, 0);
lean_inc_ref(v_toCommandContextInfo_762_);
lean_dec_ref(v_ci_741_);
v_declName_763_ = lean_ctor_get(v_expr_752_, 0);
lean_inc_n(v_declName_763_, 2);
lean_dec_ref_known(v_expr_752_, 2);
v_env_764_ = lean_ctor_get(v_toCommandContextInfo_762_, 0);
lean_inc_ref(v_env_764_);
lean_dec_ref(v_toCommandContextInfo_762_);
v___x_765_ = l_Lean_findInternalDocString_x3f(v_env_764_, v_declName_763_, v___x_740_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_749_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_784_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_784_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_784_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v_declName_763_);
lean_del_object(v___x_755_);
lean_dec(v_stx_753_);
v___x_770_ = lean_box(0);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec_ref_known(v_a_766_, 1);
lean_del_object(v___x_768_);
v___x_774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__1);
v___x_775_ = 0;
v___x_776_ = l_Lean_MessageData_ofConstName(v_declName_763_, v___x_775_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 7);
lean_ctor_set(v___x_755_, 1, v___x_776_);
lean_ctor_set(v___x_755_, 0, v___x_774_);
v___x_778_ = v___x_755_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_783_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___closed__3);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Linter_linter_tactic_docsOnAlt;
v___x_782_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v___x_781_, v_stx_753_, v___x_780_, v___y_744_, v___y_745_);
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_declName_763_);
lean_dec(v_stx_753_);
v_a_785_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_801_ == 0)
{
v___x_787_ = v___x_765_;
v_isShared_788_ = v_isSharedCheck_801_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_765_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_801_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_ref_789_ = lean_ctor_get(v___y_744_, 7);
v___x_790_ = lean_io_error_to_string(v_a_785_);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 3);
lean_ctor_set(v___x_749_, 0, v___x_790_);
v___x_792_ = v___x_749_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_800_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = l_Lean_MessageData_ofFormat(v___x_792_);
lean_inc(v_ref_789_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_793_);
lean_ctor_set(v___x_755_, 0, v_ref_789_);
v___x_795_ = v___x_755_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_ref_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_795_);
v___x_797_ = v___x_787_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_del_object(v___x_755_);
lean_dec(v_stx_753_);
lean_dec_ref(v_expr_752_);
lean_dec_ref(v_ci_741_);
v___x_802_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 0);
lean_ctor_set(v___x_749_, 0, v___x_802_);
v___x_804_ = v___x_749_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
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
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_info_742_);
lean_dec_ref(v_ci_741_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___boxed(lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_ci_813_, lean_object* v_info_814_, lean_object* v_x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
uint8_t v___x_8594__boxed_819_; lean_object* v_res_820_; 
v___x_8594__boxed_819_ = lean_unbox(v___x_812_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1(v___x_811_, v___x_8594__boxed_819_, v_ci_813_, v_info_814_, v_x_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v___x_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0(uint8_t v___x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(v___x_821_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0___boxed(lean_object* v___x_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_8734__boxed_837_; lean_object* v_res_838_; 
v___x_8734__boxed_837_ = lean_unbox(v___x_830_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0(v___x_8734__boxed_837_, v_x_831_, v_x_832_, v_x_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5(uint8_t v___x_839_, lean_object* v___x_840_, lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_dec_ref(v___x_840_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v_b_844_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_850_ = lean_box(v___x_839_);
v___f_851_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__0___boxed), 7, 1);
lean_closure_set(v___f_851_, 0, v___x_850_);
v___x_852_ = lean_box(v___x_839_);
lean_inc_ref(v___x_840_);
v___f_853_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___lam__1___boxed), 8, 2);
lean_closure_set(v___f_853_, 0, v___x_840_);
lean_closure_set(v___f_853_, 1, v___x_852_);
v___x_854_ = lean_box(0);
v_a_855_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
v___x_856_ = lean_box(0);
lean_inc(v_a_855_);
v___x_857_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v___f_851_, v___f_853_, v___x_856_, v_a_855_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_857_) == 0)
{
size_t v___x_858_; size_t v___x_859_; 
lean_dec_ref_known(v___x_857_, 1);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_843_, v___x_858_);
v_i_843_ = v___x_859_;
v_b_844_ = v___x_854_;
goto _start;
}
else
{
lean_dec_ref(v___x_840_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5___boxed(lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v_as_863_, lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_8759__boxed_870_; size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v___x_8759__boxed_870_ = lean_unbox(v___x_861_);
v_sz_boxed_871_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_872_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5(v___x_8759__boxed_870_, v___x_862_, v_as_863_, v_sz_boxed_871_, v_i_boxed_872_, v_b_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v_as_863_);
return v_res_873_;
}
}
static lean_object* _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(lean_object* v___f_878_, lean_object* v___f_879_, lean_object* v___f_880_, lean_object* v_stx_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_945_; 
v___x_885_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___y_882_, v___y_883_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_945_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_945_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_945_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
uint8_t v___x_890_; 
v___x_890_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(v_a_886_);
lean_dec(v_a_886_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec(v_stx_881_);
lean_dec_ref(v___f_880_);
lean_dec_ref(v___f_879_);
lean_dec_ref(v___f_878_);
v___x_891_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_895_; 
lean_inc(v_stx_881_);
v___x_895_ = l_Lean_Syntax_find_x3f(v_stx_881_, v___f_878_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_stx_881_);
lean_dec_ref(v___f_880_);
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_n(v_val_896_, 2);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0));
v___x_898_ = l_Lean_Syntax_find_x3f(v_val_896_, v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_901_; 
lean_dec(v_val_896_);
lean_dec_ref(v___f_879_);
v___x_899_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_899_);
v___x_901_ = v___x_888_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; 
lean_dec_ref_known(v___x_898_, 1);
v___x_903_ = l_Lean_Syntax_find_x3f(v_val_896_, v___f_879_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_del_object(v___x_888_);
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = lean_obj_once(&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2, &l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2_once, _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2);
v___x_906_ = l_Lean_Linter_linter_tactic_docsOnAlt;
v___x_907_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v___x_906_, v_val_904_, v___x_905_, v___y_882_, v___y_883_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
lean_dec(v___x_903_);
v___x_908_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_908_);
v___x_910_ = v___x_888_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_912_; 
lean_dec(v___x_895_);
lean_dec_ref(v___f_879_);
v___x_912_ = l_Lean_Syntax_find_x3f(v_stx_881_, v___f_880_);
if (lean_obj_tag(v___x_912_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_val_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unsigned_to_nat(2u);
v___x_915_ = l_Lean_Syntax_getArg(v_val_913_, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0));
v___x_917_ = l_Lean_Syntax_find_x3f(v___x_915_, v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec(v_val_913_);
v___x_918_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_918_);
v___x_920_ = v___x_888_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_infoState_926_; lean_object* v_trees_927_; lean_object* v___x_928_; lean_object* v___x_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; 
lean_dec_ref_known(v___x_917_, 1);
lean_del_object(v___x_888_);
v___x_922_ = lean_unsigned_to_nat(4u);
v___x_923_ = l_Lean_Syntax_getArg(v_val_913_, v___x_922_);
lean_dec(v_val_913_);
v___x_924_ = l_Lean_Syntax_getArgs(v___x_923_);
lean_dec(v___x_923_);
v___x_925_ = lean_st_ref_get(v___y_883_);
v_infoState_926_ = lean_ctor_get(v___x_925_, 8);
lean_inc_ref(v_infoState_926_);
lean_dec(v___x_925_);
v_trees_927_ = lean_ctor_get(v_infoState_926_, 2);
lean_inc_ref(v_trees_927_);
lean_dec_ref(v_infoState_926_);
v___x_928_ = l_Lean_PersistentArray_toArray___redArg(v_trees_927_);
lean_dec_ref(v_trees_927_);
v___x_929_ = lean_box(0);
v_sz_930_ = lean_array_size(v___x_928_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__5(v___x_890_, v___x_924_, v___x_928_, v_sz_930_, v___x_931_, v___x_929_, v___y_882_, v___y_883_);
lean_dec_ref(v___x_928_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_932_, 0);
lean_dec(v_unused_940_);
v___x_934_ = v___x_932_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_932_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_929_);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_929_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
return v___x_932_;
}
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v___x_912_);
v___x_941_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_941_);
v___x_943_ = v___x_888_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed(lean_object* v___f_946_, lean_object* v___f_947_, lean_object* v___f_948_, lean_object* v_stx_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(v___f_946_, v___f_947_, v___f_948_, v_stx_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1(lean_object* v_o_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___redArg(v_o_994_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1___boxed(lean_object* v_o_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__1(v_o_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___redArg(v_msg_1005_, v___y_1006_, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__9(v_00_u03b1_1010_, v_msg_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7(lean_object* v_00_u03b1_1016_, lean_object* v_preNode_1017_, lean_object* v_postNode_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___redArg(v_preNode_1017_, v_postNode_1018_, v_x_1019_, v_x_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_preNode_1026_, lean_object* v_postNode_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7(v_00_u03b1_1025_, v_preNode_1026_, v_postNode_1027_, v_x_1028_, v_x_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8(lean_object* v_msgData_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___redArg(v_msgData_1034_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8___boxed(lean_object* v_msgData_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__3_spec__4_spec__8(v_msgData_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_1044_, lean_object* v_preNode_1045_, lean_object* v_postNode_1046_, lean_object* v___x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___redArg(v_preNode_1045_, v_postNode_1046_, v___x_1047_, v_x_1048_, v_x_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_preNode_1055_, lean_object* v_postNode_1056_, lean_object* v___x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4_spec__7_spec__10(v_00_u03b1_1054_, v_preNode_1055_, v_postNode_1056_, v___x_1057_, v_x_1058_, v_x_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt));
v___x_1066_ = l_Lean_Elab_Command_addLinter(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2____boxed(lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
return v_res_1068_;
}
}
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_DocsOnAlt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_tactic_docsOnAlt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_tactic_docsOnAlt);
lean_dec_ref(res);
res = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_DocsOnAlt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_DocsOnAlt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_DocsOnAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_DocsOnAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_DocsOnAlt(builtin);
}
#ifdef __cplusplus
}
#endif
