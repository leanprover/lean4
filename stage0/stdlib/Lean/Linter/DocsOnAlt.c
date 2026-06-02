// Lean compiler output
// Module: Lean.Linter.DocsOnAlt
// Imports: import Lean.Parser.Syntax public import Lean.Data.Options import Lean.Elab.Command import Lean.Linter.Init import Lean.Server.InfoUtils
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DocsOnAlt_861232146____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_isAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__2_value),((lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__5_value)}};
static const lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Documentation for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` is ignored because it is a tactic alternative."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__0));
v___x_130_ = l_Lean_Syntax_getKind(v_x_128_);
v___x_131_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___closed__6));
v___x_132_ = l_List_elem___redArg(v___x_129_, v___x_130_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2___boxed(lean_object* v_x_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__2(v_x_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(lean_object* v_o_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v_env_140_; lean_object* v___x_141_; lean_object* v_toEnvExtension_142_; lean_object* v_asyncMode_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_linterSets_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v_env_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_env_140_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_142_ = lean_ctor_get(v___x_141_, 0);
v_asyncMode_143_ = lean_ctor_get(v_toEnvExtension_142_, 2);
v___x_144_ = lean_box(1);
v___x_145_ = lean_box(0);
v_linterSets_146_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_144_, v___x_141_, v_env_140_, v_asyncMode_143_, v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_o_136_);
lean_ctor_set(v___x_147_, 1, v_linterSets_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg___boxed(lean_object* v_o_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_o_149_, v___y_150_);
lean_dec(v___y_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v_scopes_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_opts_160_; lean_object* v___x_161_; 
v___x_156_ = lean_st_ref_get(v___y_154_);
v_scopes_157_ = lean_ctor_get(v___x_156_, 2);
lean_inc(v_scopes_157_);
lean_dec(v___x_156_);
v___x_158_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_159_ = l_List_head_x21___redArg(v___x_158_, v_scopes_157_);
lean_dec(v_scopes_157_);
v_opts_160_ = lean_ctor_get(v___x_159_, 1);
lean_inc_ref(v_opts_160_);
lean_dec(v___x_159_);
v___x_161_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_opts_160_, v___y_154_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0___boxed(lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_165_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0(uint8_t v___y_167_, uint8_t v_suppressElabErrors_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 1)
{
lean_object* v_pre_170_; 
v_pre_170_ = lean_ctor_get(v_x_169_, 0);
if (lean_obj_tag(v_pre_170_) == 0)
{
lean_object* v_str_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_str_171_ = lean_ctor_get(v_x_169_, 1);
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_173_ = lean_string_dec_eq(v_str_171_, v___x_172_);
if (v___x_173_ == 0)
{
return v___y_167_;
}
else
{
return v_suppressElabErrors_168_;
}
}
else
{
return v___y_167_;
}
}
else
{
return v___y_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v___y_174_, lean_object* v_suppressElabErrors_175_, lean_object* v_x_176_){
_start:
{
uint8_t v___y_8751__boxed_177_; uint8_t v_suppressElabErrors_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v___y_8751__boxed_177_ = lean_unbox(v___y_174_);
v_suppressElabErrors_boxed_178_ = lean_unbox(v_suppressElabErrors_175_);
v_res_179_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0(v___y_8751__boxed_177_, v_suppressElabErrors_boxed_178_, v_x_176_);
lean_dec(v_x_176_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__0);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
lean_ctor_set(v___x_186_, 2, v___x_185_);
lean_ctor_set(v___x_186_, 3, v___x_185_);
lean_ctor_set(v___x_186_, 4, v___x_184_);
lean_ctor_set(v___x_186_, 5, v___x_184_);
lean_ctor_set(v___x_186_, 6, v___x_184_);
lean_ctor_set(v___x_186_, 7, v___x_184_);
lean_ctor_set(v___x_186_, 8, v___x_184_);
lean_ctor_set(v___x_186_, 9, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(32u);
v___x_188_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_190_ = ((size_t)5ULL);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_unsigned_to_nat(32u);
v___x_193_ = lean_mk_empty_array_with_capacity(v___x_192_);
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__3);
v___x_195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_191_);
lean_ctor_set(v___x_195_, 3, v___x_191_);
lean_ctor_set_usize(v___x_195_, 4, v___x_190_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_196_ = lean_box(1);
v___x_197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__4);
v___x_198_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__1);
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_msgData_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v_env_204_; lean_object* v___x_205_; lean_object* v_scopes_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_opts_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_203_ = lean_st_ref_get(v___y_201_);
v_env_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_env_204_);
lean_dec(v___x_203_);
v___x_205_ = lean_st_ref_get(v___y_201_);
v_scopes_206_ = lean_ctor_get(v___x_205_, 2);
lean_inc(v_scopes_206_);
lean_dec(v___x_205_);
v___x_207_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_208_ = l_List_head_x21___redArg(v___x_207_, v_scopes_206_);
lean_dec(v_scopes_206_);
v_opts_209_ = lean_ctor_get(v___x_208_, 1);
lean_inc_ref(v_opts_209_);
lean_dec(v___x_208_);
v___x_210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__2);
v___x_211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___closed__5);
v___x_212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_212_, 0, v_env_204_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_211_);
lean_ctor_set(v___x_212_, 3, v_opts_209_);
v___x_213_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_msgData_200_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v_msgData_215_, v___y_216_);
lean_dec(v___y_216_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
lean_object* v_name_221_; lean_object* v_defValue_222_; lean_object* v_map_223_; lean_object* v___x_224_; 
v_name_221_ = lean_ctor_get(v_opt_220_, 0);
v_defValue_222_ = lean_ctor_get(v_opt_220_, 1);
v_map_223_ = lean_ctor_get(v_opts_219_, 0);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_223_, v_name_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
uint8_t v___x_225_; 
v___x_225_ = lean_unbox(v_defValue_222_);
return v___x_225_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_224_, 1);
if (lean_obj_tag(v_val_226_) == 1)
{
uint8_t v_v_227_; 
v_v_227_ = lean_ctor_get_uint8(v_val_226_, 0);
lean_dec_ref_known(v_val_226_, 0);
return v_v_227_;
}
else
{
uint8_t v___x_228_; 
lean_dec(v_val_226_);
v___x_228_ = lean_unbox(v_defValue_222_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_229_, lean_object* v_opt_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(v_opts_229_, v_opt_230_);
lean_dec_ref(v_opt_230_);
lean_dec_ref(v_opts_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(lean_object* v_ref_234_, lean_object* v_msgData_235_, uint8_t v_severity_236_, uint8_t v_isSilent_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___y_242_; uint8_t v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; uint8_t v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; uint8_t v___y_305_; uint8_t v___y_306_; uint8_t v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_333_; uint8_t v___y_334_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v___y_337_; uint8_t v___y_341_; uint8_t v___y_342_; uint8_t v___y_343_; uint8_t v___x_358_; uint8_t v___y_360_; uint8_t v___y_361_; uint8_t v___y_362_; uint8_t v___y_364_; uint8_t v___x_376_; 
v___x_358_ = 2;
v___x_376_ = l_Lean_instBEqMessageSeverity_beq(v_severity_236_, v___x_358_);
if (v___x_376_ == 0)
{
v___y_364_ = v___x_376_;
goto v___jp_363_;
}
else
{
uint8_t v___x_377_; 
lean_inc_ref(v_msgData_235_);
v___x_377_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_235_);
v___y_364_ = v___x_377_;
goto v___jp_363_;
}
v___jp_241_:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Elab_Command_getScope___redArg(v___y_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = l_Lean_Elab_Command_getScope___redArg(v___y_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_287_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_287_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_287_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_287_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v_currNamespace_258_; lean_object* v_openDecls_259_; lean_object* v_env_260_; lean_object* v_messages_261_; lean_object* v_scopes_262_; lean_object* v_usedQuotCtxts_263_; lean_object* v_nextMacroScope_264_; lean_object* v_maxRecDepth_265_; lean_object* v_ngen_266_; lean_object* v_auxDeclNGen_267_; lean_object* v_infoState_268_; lean_object* v_traceState_269_; lean_object* v_snapshotTasks_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_286_; 
v___x_257_ = lean_st_ref_take(v___y_249_);
v_currNamespace_258_ = lean_ctor_get(v_a_251_, 2);
lean_inc(v_currNamespace_258_);
lean_dec(v_a_251_);
v_openDecls_259_ = lean_ctor_get(v_a_253_, 3);
lean_inc(v_openDecls_259_);
lean_dec(v_a_253_);
v_env_260_ = lean_ctor_get(v___x_257_, 0);
v_messages_261_ = lean_ctor_get(v___x_257_, 1);
v_scopes_262_ = lean_ctor_get(v___x_257_, 2);
v_usedQuotCtxts_263_ = lean_ctor_get(v___x_257_, 3);
v_nextMacroScope_264_ = lean_ctor_get(v___x_257_, 4);
v_maxRecDepth_265_ = lean_ctor_get(v___x_257_, 5);
v_ngen_266_ = lean_ctor_get(v___x_257_, 6);
v_auxDeclNGen_267_ = lean_ctor_get(v___x_257_, 7);
v_infoState_268_ = lean_ctor_get(v___x_257_, 8);
v_traceState_269_ = lean_ctor_get(v___x_257_, 9);
v_snapshotTasks_270_ = lean_ctor_get(v___x_257_, 10);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_286_ == 0)
{
v___x_272_ = v___x_257_;
v_isShared_273_ = v_isSharedCheck_286_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_snapshotTasks_270_);
lean_inc(v_traceState_269_);
lean_inc(v_infoState_268_);
lean_inc(v_auxDeclNGen_267_);
lean_inc(v_ngen_266_);
lean_inc(v_maxRecDepth_265_);
lean_inc(v_nextMacroScope_264_);
lean_inc(v_usedQuotCtxts_263_);
lean_inc(v_scopes_262_);
lean_inc(v_messages_261_);
lean_inc(v_env_260_);
lean_dec(v___x_257_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_286_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_currNamespace_258_);
lean_ctor_set(v___x_274_, 1, v_openDecls_259_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___y_246_);
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_248_);
v___x_276_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_276_, 0, v___y_248_);
lean_ctor_set(v___x_276_, 1, v___y_245_);
lean_ctor_set(v___x_276_, 2, v___y_244_);
lean_ctor_set(v___x_276_, 3, v___y_242_);
lean_ctor_set(v___x_276_, 4, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*5, v___y_247_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*5 + 1, v___y_243_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*5 + 2, v_isSilent_237_);
v___x_277_ = l_Lean_MessageLog_add(v___x_276_, v_messages_261_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_277_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_env_260_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_scopes_262_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_usedQuotCtxts_263_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_nextMacroScope_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v_maxRecDepth_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_ngen_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 7, v_auxDeclNGen_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 8, v_infoState_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 9, v_traceState_269_);
lean_ctor_set(v_reuseFailAlloc_285_, 10, v_snapshotTasks_270_);
v___x_279_ = v_reuseFailAlloc_285_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_280_ = lean_st_ref_set(v___y_249_, v___x_279_);
v___x_281_ = lean_box(0);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_281_);
v___x_283_ = v___x_255_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_a_251_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
v_a_288_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_252_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_252_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
v_a_296_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_250_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_250_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
v___jp_304_:
{
lean_object* v_fileName_310_; lean_object* v_fileMap_311_; uint8_t v_suppressElabErrors_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_331_; 
v_fileName_310_ = lean_ctor_get(v___y_238_, 0);
v_fileMap_311_ = lean_ctor_get(v___y_238_, 1);
v_suppressElabErrors_312_ = lean_ctor_get_uint8(v___y_238_, sizeof(void*)*10);
v___x_313_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_235_);
v___x_314_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v___x_313_, v___y_239_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_331_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_331_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_331_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc_ref_n(v_fileMap_311_, 2);
v___x_319_ = l_Lean_FileMap_toPosition(v_fileMap_311_, v___y_308_);
lean_dec(v___y_308_);
v___x_320_ = l_Lean_FileMap_toPosition(v_fileMap_311_, v___y_309_);
lean_dec(v___y_309_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___x_322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_312_ == 0)
{
lean_del_object(v___x_317_);
v___y_242_ = v___x_322_;
v___y_243_ = v___y_306_;
v___y_244_ = v___x_321_;
v___y_245_ = v___x_319_;
v___y_246_ = v_a_315_;
v___y_247_ = v___y_307_;
v___y_248_ = v_fileName_310_;
v___y_249_ = v___y_239_;
goto v___jp_241_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___f_325_; uint8_t v___x_326_; 
v___x_323_ = lean_box(v___y_305_);
v___x_324_ = lean_box(v_suppressElabErrors_312_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_325_, 0, v___x_323_);
lean_closure_set(v___f_325_, 1, v___x_324_);
lean_inc(v_a_315_);
v___x_326_ = l_Lean_MessageData_hasTag(v___f_325_, v_a_315_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec_ref_known(v___x_321_, 1);
lean_dec_ref(v___x_319_);
lean_dec(v_a_315_);
v___x_327_ = lean_box(0);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_327_);
v___x_329_ = v___x_317_;
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
else
{
lean_del_object(v___x_317_);
v___y_242_ = v___x_322_;
v___y_243_ = v___y_306_;
v___y_244_ = v___x_321_;
v___y_245_ = v___x_319_;
v___y_246_ = v_a_315_;
v___y_247_ = v___y_307_;
v___y_248_ = v_fileName_310_;
v___y_249_ = v___y_239_;
goto v___jp_241_;
}
}
}
}
v___jp_332_:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Syntax_getTailPos_x3f(v___y_335_, v___y_336_);
lean_dec(v___y_335_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_inc(v___y_337_);
v___y_305_ = v___y_333_;
v___y_306_ = v___y_334_;
v___y_307_ = v___y_336_;
v___y_308_ = v___y_337_;
v___y_309_ = v___y_337_;
goto v___jp_304_;
}
else
{
lean_object* v_val_339_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v___x_338_, 1);
v___y_305_ = v___y_333_;
v___y_306_ = v___y_334_;
v___y_307_ = v___y_336_;
v___y_308_ = v___y_337_;
v___y_309_ = v_val_339_;
goto v___jp_304_;
}
}
v___jp_340_:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Elab_Command_getRef___redArg(v___y_238_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_ref_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v_ref_346_ = l_Lean_replaceRef(v_ref_234_, v_a_345_);
lean_dec(v_a_345_);
v___x_347_ = l_Lean_Syntax_getPos_x3f(v_ref_346_, v___y_342_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___y_333_ = v___y_341_;
v___y_334_ = v___y_343_;
v___y_335_ = v_ref_346_;
v___y_336_ = v___y_342_;
v___y_337_ = v___x_348_;
goto v___jp_332_;
}
else
{
lean_object* v_val_349_; 
v_val_349_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v___x_347_, 1);
v___y_333_ = v___y_341_;
v___y_334_ = v___y_343_;
v___y_335_ = v_ref_346_;
v___y_336_ = v___y_342_;
v___y_337_ = v_val_349_;
goto v___jp_332_;
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_msgData_235_);
v_a_350_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_344_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_344_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
v___jp_359_:
{
if (v___y_362_ == 0)
{
v___y_341_ = v___y_360_;
v___y_342_ = v___y_361_;
v___y_343_ = v_severity_236_;
goto v___jp_340_;
}
else
{
v___y_341_ = v___y_360_;
v___y_342_ = v___y_361_;
v___y_343_ = v___x_358_;
goto v___jp_340_;
}
}
v___jp_363_:
{
if (v___y_364_ == 0)
{
lean_object* v___x_365_; lean_object* v_scopes_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_opts_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_365_ = lean_st_ref_get(v___y_239_);
v_scopes_366_ = lean_ctor_get(v___x_365_, 2);
lean_inc(v_scopes_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_368_ = l_List_head_x21___redArg(v___x_367_, v_scopes_366_);
lean_dec(v_scopes_366_);
v_opts_369_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_opts_369_);
lean_dec(v___x_368_);
v___x_370_ = 1;
v___x_371_ = l_Lean_instBEqMessageSeverity_beq(v_severity_236_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v_opts_369_);
v___y_360_ = v___y_364_;
v___y_361_ = v___y_364_;
v___y_362_ = v___x_371_;
goto v___jp_359_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_warningAsError;
v___x_373_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__8(v_opts_369_, v___x_372_);
lean_dec_ref(v_opts_369_);
v___y_360_ = v___y_364_;
v___y_361_ = v___y_364_;
v___y_362_ = v___x_373_;
goto v___jp_359_;
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec_ref(v_msgData_235_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_378_, lean_object* v_msgData_379_, lean_object* v_severity_380_, lean_object* v_isSilent_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v_severity_boxed_385_; uint8_t v_isSilent_boxed_386_; lean_object* v_res_387_; 
v_severity_boxed_385_ = lean_unbox(v_severity_380_);
v_isSilent_boxed_386_ = lean_unbox(v_isSilent_381_);
v_res_387_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(v_ref_378_, v_msgData_379_, v_severity_boxed_385_, v_isSilent_boxed_386_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v_ref_378_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(lean_object* v_ref_388_, lean_object* v_msgData_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; 
v___x_393_ = 1;
v___x_394_ = 0;
v___x_395_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3(v_ref_388_, v_msgData_389_, v___x_393_, v___x_394_, v___y_390_, v___y_391_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2___boxed(lean_object* v_ref_396_, lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(v_ref_396_, v_msgData_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v_ref_396_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__0));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__2));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(lean_object* v_linterOption_408_, lean_object* v_stx_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_name_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_431_; 
v_name_414_ = lean_ctor_get(v_linterOption_408_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_linterOption_408_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_linterOption_408_, 1);
lean_dec(v_unused_432_);
v___x_416_ = v_linterOption_408_;
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_name_414_);
lean_dec(v_linterOption_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_418_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__1);
lean_inc(v_name_414_);
v___x_419_ = l_Lean_MessageData_ofName(v_name_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 7);
lean_ctor_set(v___x_416_, 1, v___x_419_);
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_430_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_disable_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_422_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___closed__3);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v_disable_424_ = l_Lean_MessageData_note(v___x_423_);
v___x_425_ = l_Lean_Linter_linterMessageTag;
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v_msg_410_);
lean_ctor_set(v___x_426_, 1, v_disable_424_);
v___x_427_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_428_, 0, v_name_414_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2(v_stx_409_, v___x_428_, v___y_411_, v___y_412_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1___boxed(lean_object* v_linterOption_433_, lean_object* v_stx_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v_linterOption_433_, v_stx_434_, v_msg_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v_stx_434_);
return v_res_439_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(lean_object* v_a_440_, lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
lean_inc(v___x_445_);
lean_inc(v_a_440_);
v___x_446_ = l_Lean_Syntax_structEq(v_a_440_, v___x_445_);
if (v___x_446_ == 0)
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_442_, v___x_447_);
v_i_442_ = v___x_448_;
goto _start;
}
else
{
lean_dec(v_a_440_);
return v___x_446_;
}
}
else
{
uint8_t v___x_450_; 
lean_dec(v_a_440_);
v___x_450_ = 0;
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4___boxed(lean_object* v_a_451_, lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_stop_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(v_a_451_, v_as_452_, v_i_boxed_455_, v_stop_boxed_456_);
lean_dec_ref(v_as_452_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(lean_object* v_as_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_get_size(v_as_459_);
v___x_463_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_a_460_);
return v___x_463_;
}
else
{
if (v___x_463_ == 0)
{
lean_dec(v_a_460_);
return v___x_463_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = ((size_t)0ULL);
v___x_465_ = lean_usize_of_nat(v___x_462_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2_spec__4(v_a_460_, v_as_459_, v___x_464_, v___x_465_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2___boxed(lean_object* v_as_467_, lean_object* v_a_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v_as_467_, v_a_468_);
lean_dec_ref(v_as_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__0));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__2));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1(lean_object* v___x_477_, uint8_t v___x_478_, lean_object* v_ci_479_, lean_object* v_info_480_, lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
if (lean_obj_tag(v_info_480_) == 1)
{
lean_object* v_i_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_547_; 
v_i_485_ = lean_ctor_get(v_info_480_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_info_480_);
if (v_isSharedCheck_547_ == 0)
{
v___x_487_ = v_info_480_;
v_isShared_488_ = v_isSharedCheck_547_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_i_485_);
lean_dec(v_info_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_547_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_toElabInfo_489_; lean_object* v_expr_490_; lean_object* v_stx_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_545_; 
v_toElabInfo_489_ = lean_ctor_get(v_i_485_, 0);
lean_inc_ref(v_toElabInfo_489_);
v_expr_490_ = lean_ctor_get(v_i_485_, 3);
lean_inc_ref(v_expr_490_);
lean_dec_ref(v_i_485_);
v_stx_491_ = lean_ctor_get(v_toElabInfo_489_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_toElabInfo_489_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_toElabInfo_489_, 0);
lean_dec(v_unused_546_);
v___x_493_ = v_toElabInfo_489_;
v_isShared_494_ = v_isSharedCheck_545_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_stx_491_);
lean_dec(v_toElabInfo_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_545_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
lean_inc(v_stx_491_);
v___x_495_ = l_Array_contains___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__2(v___x_477_, v_stx_491_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_498_; 
lean_del_object(v___x_493_);
lean_dec(v_stx_491_);
lean_dec_ref(v_expr_490_);
lean_dec_ref(v_ci_479_);
v___x_496_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 0);
lean_ctor_set(v___x_487_, 0, v___x_496_);
v___x_498_ = v___x_487_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
if (lean_obj_tag(v_expr_490_) == 4)
{
lean_object* v_toCommandContextInfo_500_; lean_object* v_declName_501_; lean_object* v_env_502_; lean_object* v___x_503_; 
v_toCommandContextInfo_500_ = lean_ctor_get(v_ci_479_, 0);
lean_inc_ref(v_toCommandContextInfo_500_);
lean_dec_ref(v_ci_479_);
v_declName_501_ = lean_ctor_get(v_expr_490_, 0);
lean_inc_n(v_declName_501_, 2);
lean_dec_ref_known(v_expr_490_, 2);
v_env_502_ = lean_ctor_get(v_toCommandContextInfo_500_, 0);
lean_inc_ref(v_env_502_);
lean_dec_ref(v_toCommandContextInfo_500_);
v___x_503_ = l_Lean_findInternalDocString_x3f(v_env_502_, v_declName_501_, v___x_478_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_523_; 
lean_del_object(v___x_487_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
if (lean_obj_tag(v_a_504_) == 0)
{
lean_dec(v_declName_501_);
lean_del_object(v___x_493_);
lean_dec(v_stx_491_);
goto v___jp_508_;
}
else
{
lean_dec_ref_known(v_a_504_, 1);
if (v___x_495_ == 0)
{
lean_dec(v_declName_501_);
lean_del_object(v___x_493_);
lean_dec(v_stx_491_);
goto v___jp_508_;
}
else
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
lean_del_object(v___x_506_);
v___x_513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__1);
v___x_514_ = 0;
v___x_515_ = l_Lean_MessageData_ofConstName(v_declName_501_, v___x_514_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 7);
lean_ctor_set(v___x_493_, 1, v___x_515_);
lean_ctor_set(v___x_493_, 0, v___x_513_);
v___x_517_ = v___x_493_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_522_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___closed__3);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_Linter_linter_tactic_docsOnAlt;
v___x_521_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___x_520_, v_stx_491_, v___x_519_, v___y_482_, v___y_483_);
lean_dec(v_stx_491_);
return v___x_521_;
}
}
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_declName_501_);
lean_dec(v_stx_491_);
v_a_524_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_540_ == 0)
{
v___x_526_ = v___x_503_;
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_503_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_ref_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v_ref_528_ = lean_ctor_get(v___y_482_, 7);
v___x_529_ = lean_io_error_to_string(v_a_524_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 3);
lean_ctor_set(v___x_487_, 0, v___x_529_);
v___x_531_ = v___x_487_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_539_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_MessageData_ofFormat(v___x_531_);
lean_inc(v_ref_528_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_532_);
lean_ctor_set(v___x_493_, 0, v_ref_528_);
v___x_534_ = v___x_493_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_ref_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_534_);
v___x_536_ = v___x_526_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_del_object(v___x_493_);
lean_dec(v_stx_491_);
lean_dec_ref(v_expr_490_);
lean_dec_ref(v_ci_479_);
v___x_541_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 0);
lean_ctor_set(v___x_487_, 0, v___x_541_);
v___x_543_ = v___x_487_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_info_480_);
lean_dec_ref(v_ci_479_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_ci_552_, lean_object* v_info_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_9243__boxed_558_; lean_object* v_res_559_; 
v___x_9243__boxed_558_ = lean_unbox(v___x_551_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1(v___x_550_, v___x_9243__boxed_558_, v_ci_552_, v_info_553_, v_x_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v_x_554_);
lean_dec_ref(v___x_550_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(uint8_t v___x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(v___x_560_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed(lean_object* v___x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_9384__boxed_576_; lean_object* v_res_577_; 
v___x_9384__boxed_576_ = lean_unbox(v___x_569_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0(v___x_9384__boxed_576_, v_x_570_, v_x_571_, v_x_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_x_572_);
lean_dec_ref(v_x_571_);
lean_dec_ref(v_x_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0(lean_object* v_postNode_578_, lean_object* v_ci_579_, lean_object* v_i_580_, lean_object* v_cs_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
v___x_586_ = lean_apply_6(v_postNode_578_, v_ci_579_, v_i_580_, v_cs_581_, v___y_583_, v___y_584_, lean_box(0));
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0___boxed(lean_object* v_postNode_587_, lean_object* v_ci_588_, lean_object* v_i_589_, lean_object* v_cs_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0(v_postNode_587_, v_ci_588_, v_i_589_, v_cs_590_, v_x_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v_x_591_);
return v_res_595_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_instMonadEIO(lean_box(0));
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_toApplicative_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_636_; 
v___x_603_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__0);
v___x_604_ = l_StateRefT_x27_instMonad___redArg(v___x_603_);
v_toApplicative_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_604_, 1);
lean_dec(v_unused_637_);
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_636_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_toApplicative_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_636_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_toFunctor_609_; lean_object* v_toSeq_610_; lean_object* v_toSeqLeft_611_; lean_object* v_toSeqRight_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_634_; 
v_toFunctor_609_ = lean_ctor_get(v_toApplicative_605_, 0);
v_toSeq_610_ = lean_ctor_get(v_toApplicative_605_, 2);
v_toSeqLeft_611_ = lean_ctor_get(v_toApplicative_605_, 3);
v_toSeqRight_612_ = lean_ctor_get(v_toApplicative_605_, 4);
v_isSharedCheck_634_ = !lean_is_exclusive(v_toApplicative_605_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_dec(v_unused_635_);
v___x_614_ = v_toApplicative_605_;
v_isShared_615_ = v_isSharedCheck_634_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_toSeqRight_612_);
lean_inc(v_toSeqLeft_611_);
lean_inc(v_toSeq_610_);
lean_inc(v_toFunctor_609_);
lean_dec(v_toApplicative_605_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_634_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_625_; 
v___f_616_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__1));
v___f_617_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___closed__2));
lean_inc_ref(v_toFunctor_609_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_618_, 0, v_toFunctor_609_);
v___f_619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_619_, 0, v_toFunctor_609_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___f_618_);
lean_ctor_set(v___x_620_, 1, v___f_619_);
v___f_621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_621_, 0, v_toSeqRight_612_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_622_, 0, v_toSeqLeft_611_);
v___f_623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_623_, 0, v_toSeq_610_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v___f_621_);
lean_ctor_set(v___x_614_, 3, v___f_622_);
lean_ctor_set(v___x_614_, 2, v___f_623_);
lean_ctor_set(v___x_614_, 1, v___f_616_);
lean_ctor_set(v___x_614_, 0, v___x_620_);
v___x_625_ = v___x_614_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___f_616_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v___f_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v___f_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v___f_621_);
v___x_625_ = v_reuseFailAlloc_633_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___f_617_);
lean_ctor_set(v___x_607_, 0, v___x_625_);
v___x_627_ = v___x_607_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___f_617_);
v___x_627_ = v_reuseFailAlloc_632_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_7707__overap_630_; lean_object* v___x_631_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_instInhabitedOfMonad___redArg(v___x_627_, v___x_628_);
v___x_7707__overap_630_ = lean_panic_fn_borrowed(v___x_629_, v_msg_599_);
lean_dec(v___x_629_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_631_ = lean_apply_3(v___x_7707__overap_630_, v___y_600_, v___y_601_, lean_box(0));
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v_msg_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__2));
v___x_647_ = lean_unsigned_to_nat(21u);
v___x_648_ = lean_unsigned_to_nat(65u);
v___x_649_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__1));
v___x_650_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__0));
v___x_651_ = l_mkPanicMessageWithDecl(v___x_650_, v___x_649_, v___x_648_, v___x_647_, v___x_646_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(lean_object* v_preNode_652_, lean_object* v_postNode_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
switch(lean_obj_tag(v_x_655_))
{
case 0:
{
lean_object* v_i_659_; lean_object* v_t_660_; lean_object* v___x_661_; 
v_i_659_ = lean_ctor_get(v_x_655_, 0);
lean_inc_ref(v_i_659_);
v_t_660_ = lean_ctor_get(v_x_655_, 1);
lean_inc_ref(v_t_660_);
lean_dec_ref_known(v_x_655_, 2);
v___x_661_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_659_, v_x_654_);
v_x_654_ = v___x_661_;
v_x_655_ = v_t_660_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref_known(v_x_655_, 2);
lean_dec_ref(v_postNode_653_);
lean_dec_ref(v_preNode_652_);
v___x_663_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___closed__3);
v___x_664_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v___x_663_, v___y_656_, v___y_657_);
return v___x_664_;
}
else
{
lean_object* v_i_665_; lean_object* v_children_666_; lean_object* v_val_667_; lean_object* v___x_668_; 
v_i_665_ = lean_ctor_get(v_x_655_, 0);
lean_inc_ref_n(v_i_665_, 2);
v_children_666_ = lean_ctor_get(v_x_655_, 1);
lean_inc_ref_n(v_children_666_, 2);
lean_dec_ref_known(v_x_655_, 2);
v_val_667_ = lean_ctor_get(v_x_654_, 0);
lean_inc_n(v_val_667_, 2);
lean_inc_ref(v_preNode_652_);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
v___x_668_ = lean_apply_6(v_preNode_652_, v_val_667_, v_i_665_, v_children_666_, v___y_656_, v___y_657_, lean_box(0));
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; uint8_t v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_unbox(v_a_669_);
lean_dec(v_a_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_preNode_652_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_x_654_, 0);
lean_dec(v_unused_696_);
v___x_672_ = v_x_654_;
v_isShared_673_ = v_isSharedCheck_695_;
goto v_resetjp_671_;
}
else
{
lean_dec(v_x_654_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_695_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(0);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
v___x_675_ = lean_apply_7(v_postNode_653_, v_val_667_, v_i_665_, v_children_666_, v___x_674_, v___y_656_, v___y_657_, lean_box(0));
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_a_676_);
v___x_681_ = v___x_672_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_del_object(v___x_672_);
v_a_687_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_675_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_675_);
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
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = l_Lean_Elab_Info_updateContext_x3f(v_x_654_, v_i_665_);
v___x_698_ = l_Lean_PersistentArray_toList___redArg(v_children_666_);
v___x_699_ = lean_box(0);
lean_inc_ref(v_postNode_653_);
v___x_700_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_652_, v_postNode_653_, v___x_697_, v___x_698_, v___x_699_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
v___x_702_ = lean_apply_7(v_postNode_653_, v_val_667_, v_i_665_, v_children_666_, v_a_701_, v___y_656_, v___y_657_, lean_box(0));
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_a_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_712_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_702_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_702_);
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
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_val_667_);
lean_dec_ref(v_children_666_);
lean_dec_ref(v_i_665_);
lean_dec_ref(v_postNode_653_);
v_a_720_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_700_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_700_);
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
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_val_667_);
lean_dec_ref(v_children_666_);
lean_dec_ref(v_i_665_);
lean_dec_ref_known(v_x_654_, 1);
lean_dec_ref(v_postNode_653_);
lean_dec_ref(v_preNode_652_);
v_a_728_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_668_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_668_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
default: 
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_x_654_);
lean_dec_ref(v_postNode_653_);
lean_dec_ref(v_preNode_652_);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_x_655_, 0);
lean_dec(v_unused_744_);
v___x_737_ = v_x_655_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_dec(v_x_655_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(lean_object* v_preNode_745_, lean_object* v_postNode_746_, lean_object* v___x_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_747_);
lean_dec_ref(v_postNode_746_);
lean_dec_ref(v_preNode_745_);
v___x_753_ = l_List_reverse___redArg(v_x_749_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v_head_755_; lean_object* v_tail_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_774_; 
v_head_755_ = lean_ctor_get(v_x_748_, 0);
v_tail_756_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_774_ == 0)
{
v___x_758_ = v_x_748_;
v_isShared_759_ = v_isSharedCheck_774_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_tail_756_);
lean_inc(v_head_755_);
lean_dec(v_x_748_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_774_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; 
lean_inc(v___x_747_);
lean_inc_ref(v_postNode_746_);
lean_inc_ref(v_preNode_745_);
v___x_760_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_745_, v_postNode_746_, v___x_747_, v_head_755_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_x_749_);
lean_ctor_set(v___x_758_, 0, v_a_761_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_x_749_);
v___x_763_ = v_reuseFailAlloc_765_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
v_x_748_ = v_tail_756_;
v_x_749_ = v___x_763_;
goto _start;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_758_);
lean_dec(v_tail_756_);
lean_dec(v_x_749_);
lean_dec(v___x_747_);
lean_dec_ref(v_postNode_746_);
lean_dec_ref(v_preNode_745_);
v_a_766_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_760_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_760_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_775_, lean_object* v_postNode_776_, lean_object* v___x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_775_, v_postNode_776_, v___x_777_, v_x_778_, v_x_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg___boxed(lean_object* v_preNode_784_, lean_object* v_postNode_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_784_, v_postNode_785_, v_x_786_, v_x_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(lean_object* v_preNode_792_, lean_object* v_postNode_793_, lean_object* v_ctx_x3f_794_, lean_object* v_t_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___f_799_; lean_object* v___x_800_; 
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_799_, 0, v_postNode_793_);
v___x_800_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_792_, v___f_799_, v_ctx_x3f_794_, v_t_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_809_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3___boxed(lean_object* v_preNode_818_, lean_object* v_postNode_819_, lean_object* v_ctx_x3f_820_, lean_object* v_t_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v_preNode_818_, v_postNode_819_, v_ctx_x3f_820_, v_t_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(uint8_t v___x_826_, lean_object* v___x_827_, lean_object* v_as_828_, size_t v_sz_829_, size_t v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_830_, v_sz_829_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v___x_827_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_831_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_837_ = lean_box(v___x_826_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_838_, 0, v___x_837_);
v___x_839_ = lean_box(v___x_826_);
lean_inc_ref(v___x_827_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___lam__1___boxed), 8, 2);
lean_closure_set(v___f_840_, 0, v___x_827_);
lean_closure_set(v___f_840_, 1, v___x_839_);
v_a_841_ = lean_array_uget_borrowed(v_as_828_, v_i_830_);
v___x_842_ = lean_box(0);
lean_inc(v_a_841_);
v___x_843_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3(v___f_838_, v___f_840_, v___x_842_, v_a_841_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = lean_box(0);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_830_, v___x_845_);
v_i_830_ = v___x_846_;
v_b_831_ = v___x_844_;
goto _start;
}
else
{
lean_dec_ref(v___x_827_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4___boxed(lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v_as_850_, lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___x_9824__boxed_857_; size_t v_sz_boxed_858_; size_t v_i_boxed_859_; lean_object* v_res_860_; 
v___x_9824__boxed_857_ = lean_unbox(v___x_848_);
v_sz_boxed_858_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_859_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v___x_9824__boxed_857_, v___x_849_, v_as_850_, v_sz_boxed_858_, v_i_boxed_859_, v_b_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_as_850_);
return v_res_860_;
}
}
static lean_object* _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__1));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(lean_object* v___f_865_, lean_object* v___f_866_, lean_object* v___f_867_, lean_object* v_stx_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_933_; 
v___x_872_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0(v___y_869_, v___y_870_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_933_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_933_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_933_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_885_; 
v___x_885_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_getLinterDocsOnAlt(v_a_873_);
lean_dec(v_a_873_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_del_object(v___x_875_);
lean_dec(v_stx_868_);
lean_dec_ref(v___f_867_);
lean_dec_ref(v___f_866_);
lean_dec_ref(v___f_865_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
lean_inc(v_stx_868_);
v___x_888_ = l_Lean_Syntax_find_x3f(v_stx_868_, v___f_865_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_875_);
lean_dec(v_stx_868_);
lean_dec_ref(v___f_867_);
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_n(v_val_889_, 2);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0));
v___x_891_ = l_Lean_Syntax_find_x3f(v_val_889_, v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_dec(v_val_889_);
lean_dec_ref(v___f_866_);
goto v___jp_882_;
}
else
{
lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_904_; 
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_891_, 0);
lean_dec(v_unused_905_);
v___x_893_ = v___x_891_;
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
else
{
lean_dec(v___x_891_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
if (v___x_885_ == 0)
{
lean_del_object(v___x_893_);
lean_dec(v_val_889_);
lean_dec_ref(v___f_866_);
goto v___jp_882_;
}
else
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Syntax_find_x3f(v_val_889_, v___f_866_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_del_object(v___x_893_);
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_obj_once(&l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2, &l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2_once, _init_l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__2);
v___x_898_ = l_Lean_Linter_linter_tactic_docsOnAlt;
v___x_899_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1(v___x_898_, v_val_896_, v___x_897_, v___y_869_, v___y_870_);
lean_dec(v_val_896_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_902_; 
lean_dec(v___x_895_);
v___x_900_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___x_900_);
v___x_902_ = v___x_893_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v___x_888_);
lean_dec_ref(v___f_866_);
v___x_906_ = l_Lean_Syntax_find_x3f(v_stx_868_, v___f_867_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v_val_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_val_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_907_);
lean_dec_ref_known(v___x_906_, 1);
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = l_Lean_Syntax_getArg(v_val_907_, v___x_908_);
v___x_910_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___closed__0));
v___x_911_ = l_Lean_Syntax_find_x3f(v___x_909_, v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec(v_val_907_);
goto v___jp_877_;
}
else
{
lean_dec_ref_known(v___x_911_, 1);
if (v___x_885_ == 0)
{
lean_dec(v_val_907_);
goto v___jp_877_;
}
else
{
lean_object* v___x_912_; lean_object* v_infoState_913_; lean_object* v_trees_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_875_);
v___x_912_ = lean_st_ref_get(v___y_870_);
v_infoState_913_ = lean_ctor_get(v___x_912_, 8);
lean_inc_ref(v_infoState_913_);
lean_dec(v___x_912_);
v_trees_914_ = lean_ctor_get(v_infoState_913_, 2);
lean_inc_ref(v_trees_914_);
lean_dec_ref(v_infoState_913_);
v___x_915_ = lean_unsigned_to_nat(4u);
v___x_916_ = l_Lean_Syntax_getArg(v_val_907_, v___x_915_);
lean_dec(v_val_907_);
v___x_917_ = l_Lean_Syntax_getArgs(v___x_916_);
lean_dec(v___x_916_);
v___x_918_ = l_Lean_PersistentArray_toArray___redArg(v_trees_914_);
lean_dec_ref(v_trees_914_);
v___x_919_ = lean_box(0);
v_sz_920_ = lean_array_size(v___x_918_);
v___x_921_ = ((size_t)0ULL);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__4(v___x_885_, v___x_917_, v___x_918_, v_sz_920_, v___x_921_, v___x_919_, v___y_869_, v___y_870_);
lean_dec_ref(v___x_918_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_930_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_919_);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_919_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_906_);
lean_del_object(v___x_875_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
v___jp_877_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_box(0);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
v___jp_882_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3___boxed(lean_object* v___f_934_, lean_object* v___f_935_, lean_object* v___f_936_, lean_object* v_stx_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt___lam__3(v___f_934_, v___f_935_, v___f_936_, v_stx_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0(lean_object* v_o_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___redArg(v_o_982_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0___boxed(lean_object* v_o_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__0_spec__0(v_o_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_992_, lean_object* v_msg_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___redArg(v_msg_993_, v___y_994_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_998_, lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__8(v_00_u03b1_998_, v_msg_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6(lean_object* v_00_u03b1_1004_, lean_object* v_preNode_1005_, lean_object* v_postNode_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___redArg(v_preNode_1005_, v_postNode_1006_, v_x_1007_, v_x_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_preNode_1014_, lean_object* v_postNode_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6(v_00_u03b1_1013_, v_preNode_1014_, v_postNode_1015_, v_x_1016_, v_x_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7(lean_object* v_msgData_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___redArg(v_msgData_1022_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* v_msgData_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__1_spec__2_spec__3_spec__7(v_msgData_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9(lean_object* v_00_u03b1_1032_, lean_object* v_preNode_1033_, lean_object* v_postNode_1034_, lean_object* v___x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___redArg(v_preNode_1033_, v_postNode_1034_, v___x_1035_, v_x_1036_, v_x_1037_, v___y_1038_, v___y_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_preNode_1043_, lean_object* v_postNode_1044_, lean_object* v___x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt_spec__3_spec__6_spec__9(v_00_u03b1_1042_, v_preNode_1043_, v_postNode_1044_, v___x_1045_, v_x_1046_, v_x_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_docsOnAlt));
v___x_1054_ = l_Lean_Elab_Command_addLinter(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2____boxed(lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Linter_DocsOnAlt_0__Lean_Linter_DocsOnAlt_initFn_00___x40_Lean_Linter_DocsOnAlt_3556210182____hygCtx___hyg_2_();
return v_res_1056_;
}
}
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_DocsOnAlt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
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
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
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
res = initialize_Lean_Server_InfoUtils(builtin);
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
