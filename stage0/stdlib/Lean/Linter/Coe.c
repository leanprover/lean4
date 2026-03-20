// Lean compiler output
// Module: Lean.Linter.Coe
// Imports: public import Lean.Elab.Command public import Lean.Server.InfoUtils import Lean.Linter.Basic import all Lean.Elab.Term.TermElabM
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
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default;
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedCoercions"};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(225, 120, 31, 12, 27, 111, 143, 243)}};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Validate that no deprecated coercions are used."};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Coe"};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(104, 245, 251, 188, 163, 69, 36, 187)}};
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(21, 194, 173, 54, 161, 152, 189, 121)}};
static const lean_ctor_object l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 196, 227, 214, 191, 242, 190, 69)}};
static const lean_object* l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_linter_deprecatedCoercions;
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optionCoe"};
static const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore___closed__0 = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 177, 38, 83, 111, 228, 202, 47)}};
static const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore___closed__1 = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value;
static const lean_string_object l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instCoeSubarrayArray"};
static const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore___closed__2 = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(110, 140, 157, 8, 27, 14, 210, 57)}};
static const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore___closed__3 = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value;
static const lean_array_object l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__1_value),((lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__3_value)}};
static const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore___closed__4 = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Coe_coercionsBannedInCore = (const lean_object*)&l_Lean_Linter_Coe_coercionsBannedInCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "This term uses the deprecated coercion `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5;
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "This term uses the coercion `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, which is banned in Lean's core library."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linterCoe"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 173, 243, 24, 185, 201, 144)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(185, 49, 173, 29, 145, 193, 214, 13)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__15_value),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__18_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Coe_coeLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Coe_coeLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__0_value;
static const lean_string_object l_Lean_Linter_Coe_coeLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "coeLinter"};
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__1 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__1_value;
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(104, 245, 251, 188, 163, 69, 36, 187)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2),((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 112, 251, 217, 194, 245, 186, 89)}};
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__0_value),((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value)}};
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Coe_coeLinter = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_21_ = ((lean_object*)(l_Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_22_ = ((lean_object*)(l_Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_23_ = ((lean_object*)(l_Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_24_ = l_Lean_Option_register___at___00Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0(v___x_21_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(lean_object* v_toPure_27_, lean_object* v_____do__lift_28_){
_start:
{
lean_object* v___x_29_; lean_object* v_name_30_; lean_object* v_map_31_; uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_29_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v_name_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_name_30_);
v_map_31_ = lean_ctor_get(v_____do__lift_28_, 0);
v___x_32_ = 1;
v___x_33_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_31_, v_name_30_);
lean_dec(v_name_30_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_box(v___x_32_);
v___x_35_ = lean_apply_2(v_toPure_27_, lean_box(0), v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; 
v_val_36_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_36_);
lean_dec_ref(v___x_33_);
if (lean_obj_tag(v_val_36_) == 1)
{
uint8_t v_v_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_v_37_ = lean_ctor_get_uint8(v_val_36_, 0);
lean_dec_ref(v_val_36_);
v___x_38_ = lean_box(v_v_37_);
v___x_39_ = lean_apply_2(v_toPure_27_, lean_box(0), v___x_38_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_val_36_);
v___x_40_ = lean_box(v___x_32_);
v___x_41_ = lean_apply_2(v_toPure_27_, lean_box(0), v___x_40_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed(lean_object* v_toPure_42_, lean_object* v_____do__lift_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(v_toPure_42_, v_____do__lift_43_);
lean_dec_ref(v_____do__lift_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_toApplicative_47_; lean_object* v_toBind_48_; lean_object* v_toPure_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v_toApplicative_47_ = lean_ctor_get(v_inst_45_, 0);
lean_inc_ref(v_toApplicative_47_);
v_toBind_48_ = lean_ctor_get(v_inst_45_, 1);
lean_inc(v_toBind_48_);
lean_dec_ref(v_inst_45_);
v_toPure_49_ = lean_ctor_get(v_toApplicative_47_, 1);
lean_inc(v_toPure_49_);
lean_dec_ref(v_toApplicative_47_);
v___f_50_ = lean_alloc_closure((void*)(l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_50_, 0, v_toPure_49_);
v___x_51_ = lean_apply_4(v_toBind_48_, lean_box(0), lean_box(0), v_inst_46_, v___f_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(lean_object* v_m_52_, lean_object* v_inst_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(v_inst_53_, v_inst_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; lean_object* v___x_73_; lean_object* v_mainModule_74_; lean_object* v___x_75_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = l_Lean_Environment_header(v_env_72_);
lean_dec_ref(v_env_72_);
v_mainModule_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_mainModule_74_);
lean_dec_ref(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_mainModule_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_76_);
lean_dec(v___y_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_infoState_90_; lean_object* v_trees_91_; lean_object* v___x_92_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_infoState_90_ = lean_ctor_get(v___x_89_, 8);
lean_inc_ref(v_infoState_90_);
lean_dec(v___x_89_);
v_trees_91_ = lean_ctor_get(v_infoState_90_, 2);
lean_inc_ref(v_trees_91_);
lean_dec_ref(v_infoState_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v_trees_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_93_);
lean_dec(v___y_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0(lean_object* v_postNode_104_, lean_object* v_ci_105_, lean_object* v_i_106_, lean_object* v_cs_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_apply_6(v_postNode_104_, v_ci_105_, v_i_106_, v_cs_107_, v___y_109_, v___y_110_, lean_box(0));
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0___boxed(lean_object* v_postNode_113_, lean_object* v_ci_114_, lean_object* v_i_115_, lean_object* v_cs_116_, lean_object* v_x_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0(v_postNode_113_, v_ci_114_, v_i_115_, v_cs_116_, v_x_117_, v___y_118_, v___y_119_);
lean_dec(v_x_117_);
return v_res_121_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_toApplicative_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_162_; 
v___x_129_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__0);
v___x_130_ = l_ReaderT_instMonad___redArg(v___x_129_);
v_toApplicative_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_130_, 1);
lean_dec(v_unused_163_);
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_162_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_toApplicative_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_162_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_toFunctor_135_; lean_object* v_toSeq_136_; lean_object* v_toSeqLeft_137_; lean_object* v_toSeqRight_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_160_; 
v_toFunctor_135_ = lean_ctor_get(v_toApplicative_131_, 0);
v_toSeq_136_ = lean_ctor_get(v_toApplicative_131_, 2);
v_toSeqLeft_137_ = lean_ctor_get(v_toApplicative_131_, 3);
v_toSeqRight_138_ = lean_ctor_get(v_toApplicative_131_, 4);
v_isSharedCheck_160_ = !lean_is_exclusive(v_toApplicative_131_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_dec(v_unused_161_);
v___x_140_ = v_toApplicative_131_;
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_toSeqRight_138_);
lean_inc(v_toSeqLeft_137_);
lean_inc(v_toSeq_136_);
lean_inc(v_toFunctor_135_);
lean_dec(v_toApplicative_131_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_151_; 
v___f_142_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__1));
v___f_143_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___closed__2));
lean_inc_ref(v_toFunctor_135_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_135_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toFunctor_135_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_144_);
lean_ctor_set(v___x_146_, 1, v___f_145_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqRight_138_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeqLeft_137_);
v___f_149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_149_, 0, v_toSeq_136_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 4, v___f_147_);
lean_ctor_set(v___x_140_, 3, v___f_148_);
lean_ctor_set(v___x_140_, 2, v___f_149_);
lean_ctor_set(v___x_140_, 1, v___f_142_);
lean_ctor_set(v___x_140_, 0, v___x_146_);
v___x_151_ = v___x_140_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___f_142_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v___f_149_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v___f_148_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v___f_147_);
v___x_151_ = v_reuseFailAlloc_159_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___f_143_);
lean_ctor_set(v___x_133_, 0, v___x_151_);
v___x_153_ = v___x_133_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_143_);
v___x_153_ = v_reuseFailAlloc_158_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_9367__overap_156_; lean_object* v___x_157_; 
v___x_154_ = lean_box(0);
v___x_155_ = l_instInhabitedOfMonad___redArg(v___x_153_, v___x_154_);
v___x_9367__overap_156_ = lean_panic_fn(v___x_155_, v_msg_125_);
v___x_157_ = lean_apply_3(v___x_9367__overap_156_, v___y_126_, v___y_127_, lean_box(0));
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v_msg_164_, v___y_165_, v___y_166_);
return v_res_168_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__2));
v___x_173_ = lean_unsigned_to_nat(21u);
v___x_174_ = lean_unsigned_to_nat(65u);
v___x_175_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__1));
v___x_176_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__0));
v___x_177_ = l_mkPanicMessageWithDecl(v___x_176_, v___x_175_, v___x_174_, v___x_173_, v___x_172_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(lean_object* v_preNode_178_, lean_object* v_postNode_179_, lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
switch(lean_obj_tag(v_x_181_))
{
case 0:
{
lean_object* v_i_185_; lean_object* v_t_186_; lean_object* v___x_187_; 
v_i_185_ = lean_ctor_get(v_x_181_, 0);
lean_inc_ref(v_i_185_);
v_t_186_ = lean_ctor_get(v_x_181_, 1);
lean_inc_ref(v_t_186_);
lean_dec_ref(v_x_181_);
v___x_187_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_185_, v_x_180_);
v_x_180_ = v___x_187_;
v_x_181_ = v_t_186_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec_ref(v_x_181_);
lean_dec_ref(v_postNode_179_);
lean_dec_ref(v_preNode_178_);
v___x_189_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___closed__3);
v___x_190_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v___x_189_, v___y_182_, v___y_183_);
return v___x_190_;
}
else
{
lean_object* v_i_191_; lean_object* v_children_192_; lean_object* v_val_193_; lean_object* v___x_194_; 
v_i_191_ = lean_ctor_get(v_x_181_, 0);
lean_inc_ref(v_i_191_);
v_children_192_ = lean_ctor_get(v_x_181_, 1);
lean_inc_ref(v_children_192_);
lean_dec_ref(v_x_181_);
v_val_193_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_val_193_);
lean_inc_ref(v_preNode_178_);
lean_inc(v___y_183_);
lean_inc_ref(v___y_182_);
lean_inc_ref(v_children_192_);
lean_inc_ref(v_i_191_);
lean_inc(v_val_193_);
v___x_194_ = lean_apply_6(v_preNode_178_, v_val_193_, v_i_191_, v_children_192_, v___y_182_, v___y_183_, lean_box(0));
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; uint8_t v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_unbox(v_a_195_);
lean_dec(v_a_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_preNode_178_);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v_x_180_, 0);
lean_dec(v_unused_222_);
v___x_198_ = v_x_180_;
v_isShared_199_ = v_isSharedCheck_221_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_x_180_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_221_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_7(v_postNode_179_, v_val_193_, v_i_191_, v_children_192_, v___x_200_, v___y_182_, v___y_183_, lean_box(0));
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_212_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_212_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_a_202_);
v___x_207_ = v___x_198_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_del_object(v___x_198_);
v_a_213_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_201_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_201_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = l_Lean_Elab_Info_updateContext_x3f(v_x_180_, v_i_191_);
v___x_224_ = l_Lean_PersistentArray_toList___redArg(v_children_192_);
v___x_225_ = lean_box(0);
lean_inc(v___y_183_);
lean_inc_ref(v___y_182_);
lean_inc_ref(v_postNode_179_);
v___x_226_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_178_, v_postNode_179_, v___x_223_, v___x_224_, v___x_225_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = lean_apply_7(v_postNode_179_, v_val_193_, v_i_191_, v_children_192_, v_a_227_, v___y_182_, v___y_183_, lean_box(0));
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_a_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_228_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_val_193_);
lean_dec_ref(v_children_192_);
lean_dec_ref(v_i_191_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec_ref(v_postNode_179_);
v_a_246_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_226_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_226_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
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
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_val_193_);
lean_dec_ref(v_children_192_);
lean_dec_ref(v_i_191_);
lean_dec_ref(v_x_180_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec_ref(v_postNode_179_);
lean_dec_ref(v_preNode_178_);
v_a_254_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_194_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_194_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
default: 
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v_x_180_);
lean_dec_ref(v_postNode_179_);
lean_dec_ref(v_preNode_178_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v_x_181_, 0);
lean_dec(v_unused_270_);
v___x_263_ = v_x_181_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_x_181_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_box(0);
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 0);
lean_ctor_set(v___x_263_, 0, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(lean_object* v_preNode_271_, lean_object* v_postNode_272_, lean_object* v___x_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___x_273_);
lean_dec_ref(v_postNode_272_);
lean_dec_ref(v_preNode_271_);
v___x_279_ = l_List_reverse___redArg(v_x_275_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v_head_281_; lean_object* v_tail_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_300_; 
v_head_281_ = lean_ctor_get(v_x_274_, 0);
v_tail_282_ = lean_ctor_get(v_x_274_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_300_ == 0)
{
v___x_284_ = v_x_274_;
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_tail_282_);
lean_inc(v_head_281_);
lean_dec(v_x_274_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; 
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___x_273_);
lean_inc_ref(v_postNode_272_);
lean_inc_ref(v_preNode_271_);
v___x_286_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_271_, v_postNode_272_, v___x_273_, v_head_281_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref(v___x_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_x_275_);
lean_ctor_set(v___x_284_, 0, v_a_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_287_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_x_275_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v_x_274_ = v_tail_282_;
v_x_275_ = v___x_289_;
goto _start;
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_del_object(v___x_284_);
lean_dec(v_tail_282_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v_x_275_);
lean_dec(v___x_273_);
lean_dec_ref(v_postNode_272_);
lean_dec_ref(v_preNode_271_);
v_a_292_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_286_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_286_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_preNode_301_, lean_object* v_postNode_302_, lean_object* v___x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_301_, v_postNode_302_, v___x_303_, v_x_304_, v_x_305_, v___y_306_, v___y_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg___boxed(lean_object* v_preNode_310_, lean_object* v_postNode_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_310_, v_postNode_311_, v_x_312_, v_x_313_, v___y_314_, v___y_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(lean_object* v_preNode_318_, lean_object* v_postNode_319_, lean_object* v_ctx_x3f_320_, lean_object* v_t_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_325_, 0, v_postNode_319_);
v___x_326_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_318_, v___f_325_, v_ctx_x3f_320_, v_t_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v___x_326_, 0);
lean_dec(v_unused_335_);
v___x_328_ = v___x_326_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_dec(v___x_326_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_box(0);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_326_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_326_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object* v_preNode_344_, lean_object* v_postNode_345_, lean_object* v_ctx_x3f_346_, lean_object* v_t_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(v_preNode_344_, v_postNode_345_, v_ctx_x3f_346_, v_t_347_, v___y_348_, v___y_349_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_352_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_ctor_set(v___x_357_, 3, v___x_355_);
lean_ctor_set(v___x_357_, 4, v___x_355_);
lean_ctor_set(v___x_357_, 5, v___x_355_);
lean_ctor_set(v___x_357_, 6, v___x_355_);
lean_ctor_set(v___x_357_, 7, v___x_355_);
lean_ctor_set(v___x_357_, 8, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_unsigned_to_nat(32u);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_361_ = ((size_t)5ULL);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_unsigned_to_nat(32u);
v___x_364_ = lean_mk_empty_array_with_capacity(v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_366_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_362_);
lean_ctor_set(v___x_366_, 3, v___x_362_);
lean_ctor_set_usize(v___x_366_, 4, v___x_361_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = lean_box(1);
v___x_368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_369_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
lean_ctor_set(v___x_370_, 2, v___x_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(lean_object* v_msgData_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_env_375_; lean_object* v___x_376_; lean_object* v_scopes_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_opts_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_374_ = lean_st_ref_get(v___y_372_);
v_env_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc_ref(v_env_375_);
lean_dec(v___x_374_);
v___x_376_ = lean_st_ref_get(v___y_372_);
v_scopes_377_ = lean_ctor_get(v___x_376_, 2);
lean_inc(v_scopes_377_);
lean_dec(v___x_376_);
v___x_378_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_379_ = l_List_head_x21___redArg(v___x_378_, v_scopes_377_);
lean_dec(v_scopes_377_);
v_opts_380_ = lean_ctor_get(v___x_379_, 1);
lean_inc_ref(v_opts_380_);
lean_dec(v___x_379_);
v___x_381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v_env_375_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set(v___x_383_, 3, v_opts_380_);
v___x_384_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_msgData_371_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v_msgData_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0(uint8_t v___y_391_, uint8_t v_suppressElabErrors_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 1)
{
lean_object* v_pre_394_; 
v_pre_394_ = lean_ctor_get(v_x_393_, 0);
if (lean_obj_tag(v_pre_394_) == 0)
{
lean_object* v_str_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_str_395_ = lean_ctor_get(v_x_393_, 1);
v___x_396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___closed__0));
v___x_397_ = lean_string_dec_eq(v_str_395_, v___x_396_);
if (v___x_397_ == 0)
{
return v___y_391_;
}
else
{
return v_suppressElabErrors_392_;
}
}
else
{
return v___y_391_;
}
}
else
{
return v___y_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___boxed(lean_object* v___y_398_, lean_object* v_suppressElabErrors_399_, lean_object* v_x_400_){
_start:
{
uint8_t v___y_11585__boxed_401_; uint8_t v_suppressElabErrors_boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v___y_11585__boxed_401_ = lean_unbox(v___y_398_);
v_suppressElabErrors_boxed_402_ = lean_unbox(v_suppressElabErrors_399_);
v_res_403_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0(v___y_11585__boxed_401_, v_suppressElabErrors_boxed_402_, v_x_400_);
lean_dec(v_x_400_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object* v_ref_406_, lean_object* v_msgData_407_, uint8_t v_severity_408_, uint8_t v_isSilent_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; uint8_t v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_477_; uint8_t v___y_478_; uint8_t v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_505_; uint8_t v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; uint8_t v___y_513_; uint8_t v___y_514_; uint8_t v___y_515_; uint8_t v___x_530_; uint8_t v___y_532_; uint8_t v___y_533_; uint8_t v___y_534_; uint8_t v___y_536_; uint8_t v___x_548_; 
v___x_530_ = 2;
v___x_548_ = l_Lean_instBEqMessageSeverity_beq(v_severity_408_, v___x_530_);
if (v___x_548_ == 0)
{
v___y_536_ = v___x_548_;
goto v___jp_535_;
}
else
{
uint8_t v___x_549_; 
lean_inc_ref(v_msgData_407_);
v___x_549_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_407_);
v___y_536_ = v___x_549_;
goto v___jp_535_;
}
v___jp_413_:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Elab_Command_getScope___redArg(v___y_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_Elab_Command_getScope___redArg(v___y_421_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_459_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_459_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_459_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_459_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_currNamespace_430_; lean_object* v_openDecls_431_; lean_object* v_env_432_; lean_object* v_messages_433_; lean_object* v_scopes_434_; lean_object* v_usedQuotCtxts_435_; lean_object* v_nextMacroScope_436_; lean_object* v_maxRecDepth_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_infoState_440_; lean_object* v_traceState_441_; lean_object* v_snapshotTasks_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_458_; 
v___x_429_ = lean_st_ref_take(v___y_421_);
v_currNamespace_430_ = lean_ctor_get(v_a_423_, 2);
lean_inc(v_currNamespace_430_);
lean_dec(v_a_423_);
v_openDecls_431_ = lean_ctor_get(v_a_425_, 3);
lean_inc(v_openDecls_431_);
lean_dec(v_a_425_);
v_env_432_ = lean_ctor_get(v___x_429_, 0);
v_messages_433_ = lean_ctor_get(v___x_429_, 1);
v_scopes_434_ = lean_ctor_get(v___x_429_, 2);
v_usedQuotCtxts_435_ = lean_ctor_get(v___x_429_, 3);
v_nextMacroScope_436_ = lean_ctor_get(v___x_429_, 4);
v_maxRecDepth_437_ = lean_ctor_get(v___x_429_, 5);
v_ngen_438_ = lean_ctor_get(v___x_429_, 6);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_429_, 7);
v_infoState_440_ = lean_ctor_get(v___x_429_, 8);
v_traceState_441_ = lean_ctor_get(v___x_429_, 9);
v_snapshotTasks_442_ = lean_ctor_get(v___x_429_, 10);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_458_ == 0)
{
v___x_444_ = v___x_429_;
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snapshotTasks_442_);
lean_inc(v_traceState_441_);
lean_inc(v_infoState_440_);
lean_inc(v_auxDeclNGen_439_);
lean_inc(v_ngen_438_);
lean_inc(v_maxRecDepth_437_);
lean_inc(v_nextMacroScope_436_);
lean_inc(v_usedQuotCtxts_435_);
lean_inc(v_scopes_434_);
lean_inc(v_messages_433_);
lean_inc(v_env_432_);
lean_dec(v___x_429_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_currNamespace_430_);
lean_ctor_set(v___x_446_, 1, v_openDecls_431_);
v___x_447_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___y_415_);
v___x_448_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_448_, 0, v___y_418_);
lean_ctor_set(v___x_448_, 1, v___y_414_);
lean_ctor_set(v___x_448_, 2, v___y_420_);
lean_ctor_set(v___x_448_, 3, v___y_416_);
lean_ctor_set(v___x_448_, 4, v___x_447_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*5, v___y_417_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*5 + 1, v___y_419_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*5 + 2, v_isSilent_409_);
v___x_449_ = l_Lean_MessageLog_add(v___x_448_, v_messages_433_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_449_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_env_432_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_scopes_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_usedQuotCtxts_435_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_nextMacroScope_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_maxRecDepth_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_ngen_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_infoState_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 9, v_traceState_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 10, v_snapshotTasks_442_);
v___x_451_ = v_reuseFailAlloc_457_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_st_ref_set(v___y_421_, v___x_451_);
v___x_453_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_453_);
v___x_455_ = v___x_427_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_423_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_418_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v___y_414_);
v_a_460_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_424_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_424_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v___y_420_);
lean_dec_ref(v___y_418_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v___y_414_);
v_a_468_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_422_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_422_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
v___jp_476_:
{
lean_object* v_fileName_482_; lean_object* v_fileMap_483_; uint8_t v_suppressElabErrors_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_503_; 
v_fileName_482_ = lean_ctor_get(v___y_410_, 0);
lean_inc_ref(v_fileName_482_);
v_fileMap_483_ = lean_ctor_get(v___y_410_, 1);
lean_inc_ref(v_fileMap_483_);
v_suppressElabErrors_484_ = lean_ctor_get_uint8(v___y_410_, sizeof(void*)*10);
lean_dec_ref(v___y_410_);
v___x_485_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_407_);
v___x_486_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v___x_485_, v___y_411_);
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_503_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc_ref(v_fileMap_483_);
v___x_491_ = l_Lean_FileMap_toPosition(v_fileMap_483_, v___y_480_);
lean_dec(v___y_480_);
v___x_492_ = l_Lean_FileMap_toPosition(v_fileMap_483_, v___y_481_);
lean_dec(v___y_481_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
v___x_494_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___closed__0));
if (v_suppressElabErrors_484_ == 0)
{
lean_del_object(v___x_489_);
v___y_414_ = v___x_491_;
v___y_415_ = v_a_487_;
v___y_416_ = v___x_494_;
v___y_417_ = v___y_478_;
v___y_418_ = v_fileName_482_;
v___y_419_ = v___y_479_;
v___y_420_ = v___x_493_;
v___y_421_ = v___y_411_;
goto v___jp_413_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___f_497_; uint8_t v___x_498_; 
v___x_495_ = lean_box(v___y_477_);
v___x_496_ = lean_box(v_suppressElabErrors_484_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_497_, 0, v___x_495_);
lean_closure_set(v___f_497_, 1, v___x_496_);
lean_inc(v_a_487_);
v___x_498_ = l_Lean_MessageData_hasTag(v___f_497_, v_a_487_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_501_; 
lean_dec_ref(v___x_493_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_487_);
lean_dec_ref(v_fileName_482_);
v___x_499_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_499_);
v___x_501_ = v___x_489_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_del_object(v___x_489_);
v___y_414_ = v___x_491_;
v___y_415_ = v_a_487_;
v___y_416_ = v___x_494_;
v___y_417_ = v___y_478_;
v___y_418_ = v_fileName_482_;
v___y_419_ = v___y_479_;
v___y_420_ = v___x_493_;
v___y_421_ = v___y_411_;
goto v___jp_413_;
}
}
}
}
v___jp_504_:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Syntax_getTailPos_x3f(v___y_508_, v___y_506_);
lean_dec(v___y_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_inc(v___y_509_);
v___y_477_ = v___y_505_;
v___y_478_ = v___y_506_;
v___y_479_ = v___y_507_;
v___y_480_ = v___y_509_;
v___y_481_ = v___y_509_;
goto v___jp_476_;
}
else
{
lean_object* v_val_511_; 
v_val_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v___x_510_);
v___y_477_ = v___y_505_;
v___y_478_ = v___y_506_;
v___y_479_ = v___y_507_;
v___y_480_ = v___y_509_;
v___y_481_ = v_val_511_;
goto v___jp_476_;
}
}
v___jp_512_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Elab_Command_getRef___redArg(v___y_410_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v_ref_518_; lean_object* v___x_519_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v___x_516_);
v_ref_518_ = l_Lean_replaceRef(v_ref_406_, v_a_517_);
lean_dec(v_a_517_);
v___x_519_ = l_Lean_Syntax_getPos_x3f(v_ref_518_, v___y_514_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___y_505_ = v___y_513_;
v___y_506_ = v___y_514_;
v___y_507_ = v___y_515_;
v___y_508_ = v_ref_518_;
v___y_509_ = v___x_520_;
goto v___jp_504_;
}
else
{
lean_object* v_val_521_; 
v_val_521_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_521_);
lean_dec_ref(v___x_519_);
v___y_505_ = v___y_513_;
v___y_506_ = v___y_514_;
v___y_507_ = v___y_515_;
v___y_508_ = v_ref_518_;
v___y_509_ = v_val_521_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___y_410_);
lean_dec_ref(v_msgData_407_);
v_a_522_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_516_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_516_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
v___jp_531_:
{
if (v___y_534_ == 0)
{
v___y_513_ = v___y_532_;
v___y_514_ = v___y_533_;
v___y_515_ = v_severity_408_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___y_532_;
v___y_514_ = v___y_533_;
v___y_515_ = v___x_530_;
goto v___jp_512_;
}
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
lean_object* v___x_537_; lean_object* v_scopes_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_opts_541_; uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_537_ = lean_st_ref_get(v___y_411_);
v_scopes_538_ = lean_ctor_get(v___x_537_, 2);
lean_inc(v_scopes_538_);
lean_dec(v___x_537_);
v___x_539_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_540_ = l_List_head_x21___redArg(v___x_539_, v_scopes_538_);
lean_dec(v_scopes_538_);
v_opts_541_ = lean_ctor_get(v___x_540_, 1);
lean_inc_ref(v_opts_541_);
lean_dec(v___x_540_);
v___x_542_ = 1;
v___x_543_ = l_Lean_instBEqMessageSeverity_beq(v_severity_408_, v___x_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_opts_541_);
v___y_532_ = v___y_536_;
v___y_533_ = v___y_536_;
v___y_534_ = v___x_543_;
goto v___jp_531_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = l_Lean_warningAsError;
v___x_545_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(v_opts_541_, v___x_544_);
lean_dec_ref(v_opts_541_);
v___y_532_ = v___y_536_;
v___y_533_ = v___y_536_;
v___y_534_ = v___x_545_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v___y_410_);
lean_dec_ref(v_msgData_407_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object* v_ref_550_, lean_object* v_msgData_551_, lean_object* v_severity_552_, lean_object* v_isSilent_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v_severity_boxed_557_; uint8_t v_isSilent_boxed_558_; lean_object* v_res_559_; 
v_severity_boxed_557_ = lean_unbox(v_severity_552_);
v_isSilent_boxed_558_ = lean_unbox(v_isSilent_553_);
v_res_559_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_ref_550_, v_msgData_551_, v_severity_boxed_557_, v_isSilent_boxed_558_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec(v_ref_550_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object* v_ref_560_, lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = 1;
v___x_566_ = 0;
v___x_567_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_ref_560_, v_msgData_561_, v___x_565_, v___x_566_, v___y_562_, v___y_563_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object* v_ref_568_, lean_object* v_msgData_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(v_ref_568_, v_msgData_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec(v_ref_568_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(lean_object* v_linterOption_580_, lean_object* v_stx_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_name_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_601_; 
v_name_586_ = lean_ctor_get(v_linterOption_580_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_linterOption_580_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_linterOption_580_, 1);
lean_dec(v_unused_602_);
v___x_588_ = v_linterOption_580_;
v_isShared_589_ = v_isSharedCheck_601_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_name_586_);
lean_dec(v_linterOption_580_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_601_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1);
lean_inc(v_name_586_);
v___x_591_ = l_Lean_MessageData_ofName(v_name_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 7);
lean_ctor_set(v___x_588_, 1, v___x_591_);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_600_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_disable_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v_disable_596_ = l_Lean_MessageData_note(v___x_595_);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v_msg_582_);
lean_ctor_set(v___x_597_, 1, v_disable_596_);
v___x_598_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_598_, 0, v_name_586_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(v_stx_581_, v___x_598_, v___y_583_, v___y_584_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(lean_object* v_linterOption_603_, lean_object* v_stx_604_, lean_object* v_msg_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v_linterOption_603_, v_stx_604_, v_msg_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec(v_stx_604_);
return v_res_609_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__2));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__4));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__7));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__9));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(uint8_t v___x_645_, lean_object* v_i_646_, lean_object* v_a_647_, lean_object* v_as_x27_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
if (lean_obj_tag(v_as_x27_648_) == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___y_650_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_649_);
return v___x_653_;
}
else
{
lean_object* v_head_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_700_; 
v_head_654_ = lean_ctor_get(v_as_x27_648_, 0);
v_tail_655_ = lean_ctor_get(v_as_x27_648_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_as_x27_648_);
if (v_isSharedCheck_700_ == 0)
{
v___x_657_ = v_as_x27_648_;
v_isShared_658_ = v_isSharedCheck_700_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_head_654_);
lean_dec(v_as_x27_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_700_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___x_683_; uint8_t v___y_685_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_683_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__6));
v___x_695_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__13));
v___x_696_ = lean_name_eq(v_a_647_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = l_Lean_Name_getRoot(v_a_647_);
v___x_698_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__19));
v___x_699_ = l_List_elem___redArg(v___x_683_, v___x_697_, v___x_698_);
v___y_685_ = v___x_699_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_696_;
goto v___jp_684_;
}
v___jp_661_:
{
if (v___x_645_ == 0)
{
lean_dec_ref(v___y_662_);
lean_del_object(v___x_657_);
lean_dec(v_head_654_);
v_as_x27_648_ = v_tail_655_;
v_b_649_ = v___x_659_;
goto _start;
}
else
{
lean_object* v___x_665_; lean_object* v_env_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_665_ = lean_st_ref_get(v___y_663_);
v_env_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc_ref(v_env_666_);
lean_dec(v___x_665_);
v___x_667_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_668_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_head_654_);
v___x_669_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_667_, v___x_668_, v_env_666_, v_head_654_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_stx_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_dec_ref(v___x_669_);
v_stx_670_ = lean_ctor_get(v_i_646_, 0);
v___x_671_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__1));
v___x_672_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__3);
v___x_673_ = l_Lean_MessageData_ofConstName(v_head_654_, v___x_645_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 7);
lean_ctor_set(v___x_657_, 1, v___x_673_);
lean_ctor_set(v___x_657_, 0, v___x_672_);
v___x_675_ = v___x_657_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_681_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__5);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_671_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v___x_660_, v_stx_670_, v___x_678_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec_ref(v___x_679_);
v_as_x27_648_ = v_tail_655_;
v_b_649_ = v___x_659_;
goto _start;
}
else
{
lean_dec(v_tail_655_);
lean_dec_ref(v___y_650_);
return v___x_679_;
}
}
}
else
{
lean_dec(v___x_669_);
lean_dec_ref(v___y_662_);
lean_del_object(v___x_657_);
lean_dec(v_head_654_);
v_as_x27_648_ = v_tail_655_;
v_b_649_ = v___x_659_;
goto _start;
}
}
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
lean_inc_ref(v___y_650_);
v___y_662_ = v___y_650_;
v___y_663_ = v___y_651_;
goto v___jp_661_;
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_Linter_Coe_coercionsBannedInCore));
lean_inc(v_head_654_);
v___x_687_ = l_Array_contains___redArg(v___x_683_, v___x_686_, v_head_654_);
if (v___x_687_ == 0)
{
lean_inc_ref(v___y_650_);
v___y_662_ = v___y_650_;
v___y_663_ = v___y_651_;
goto v___jp_661_;
}
else
{
lean_object* v_stx_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_stx_688_ = lean_ctor_get(v_i_646_, 0);
v___x_689_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__8);
lean_inc(v_head_654_);
v___x_690_ = l_Lean_MessageData_ofName(v_head_654_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___closed__10);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
lean_inc_ref(v___y_650_);
v___x_694_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4(v_stx_688_, v___x_693_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref(v___x_694_);
lean_inc_ref(v___y_650_);
v___y_662_ = v___y_650_;
v___y_663_ = v___y_651_;
goto v___jp_661_;
}
else
{
lean_del_object(v___x_657_);
lean_dec(v_tail_655_);
lean_dec(v_head_654_);
lean_dec_ref(v___y_650_);
return v___x_694_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg___boxed(lean_object* v___x_701_, lean_object* v_i_702_, lean_object* v_a_703_, lean_object* v_as_x27_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_11997__boxed_709_; lean_object* v_res_710_; 
v___x_11997__boxed_709_ = lean_unbox(v___x_701_);
v_res_710_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(v___x_11997__boxed_709_, v_i_702_, v_a_703_, v_as_x27_704_, v_b_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec(v_a_703_);
lean_dec_ref(v_i_702_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1(lean_object* v___x_711_, uint8_t v___x_712_, lean_object* v_a_713_, lean_object* v___x_714_, uint8_t v___x_715_, lean_object* v_x_716_, lean_object* v_info_717_, lean_object* v_x_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
if (lean_obj_tag(v_info_717_) == 10)
{
lean_object* v_i_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_751_; 
v_i_722_ = lean_ctor_get(v_info_717_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_info_717_);
if (v_isSharedCheck_751_ == 0)
{
v___x_724_ = v_info_717_;
v_isShared_725_ = v_isSharedCheck_751_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_i_722_);
lean_dec(v_info_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_751_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_value_726_; lean_object* v___x_727_; 
v_value_726_ = lean_ctor_get(v_i_722_, 1);
v___x_727_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_726_, v___x_711_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
lean_del_object(v___x_724_);
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(v___x_712_, v_i_722_, v_a_713_, v_val_728_, v___x_714_, v___y_719_, v___y_720_);
lean_dec_ref(v_i_722_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_738_);
v___x_731_ = v___x_729_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_dec(v___x_729_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_box(v___x_715_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_729_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_729_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v___x_727_);
lean_dec_ref(v_i_722_);
lean_dec_ref(v___y_719_);
v___x_747_ = lean_box(v___x_715_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 0);
lean_ctor_set(v___x_724_, 0, v___x_747_);
v___x_749_ = v___x_724_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v___y_719_);
lean_dec_ref(v_info_717_);
v___x_752_ = lean_box(v___x_715_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed(lean_object* v___x_754_, lean_object* v___x_755_, lean_object* v_a_756_, lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v_x_759_, lean_object* v_info_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v___x_12145__boxed_765_; uint8_t v___x_12148__boxed_766_; lean_object* v_res_767_; 
v___x_12145__boxed_765_ = lean_unbox(v___x_755_);
v___x_12148__boxed_766_ = lean_unbox(v___x_758_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1(v___x_754_, v___x_12145__boxed_765_, v_a_756_, v___x_757_, v___x_12148__boxed_766_, v_x_759_, v_info_760_, v_x_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v_x_761_);
lean_dec_ref(v_x_759_);
lean_dec(v_a_756_);
lean_dec(v___x_754_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0(lean_object* v___x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_768_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0___boxed(lean_object* v___x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__0(v___x_776_, v_x_777_, v_x_778_, v_x_779_, v_x_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v_x_780_);
lean_dec_ref(v_x_779_);
lean_dec_ref(v_x_778_);
lean_dec_ref(v_x_777_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(uint8_t v___x_789_, lean_object* v_a_790_, lean_object* v_as_791_, size_t v_sz_792_, size_t v_i_793_, lean_object* v_b_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_793_, v_sz_792_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v_a_790_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_794_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_b_794_);
v___x_800_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_801_ = lean_box(0);
v___f_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0));
v___x_803_ = lean_box(v___x_789_);
v___x_804_ = lean_box(v___x_798_);
lean_inc(v_a_790_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed), 11, 5);
lean_closure_set(v___f_805_, 0, v___x_800_);
lean_closure_set(v___f_805_, 1, v___x_803_);
lean_closure_set(v___f_805_, 2, v_a_790_);
lean_closure_set(v___f_805_, 3, v___x_801_);
lean_closure_set(v___f_805_, 4, v___x_804_);
v_a_806_ = lean_array_uget_borrowed(v_as_791_, v_i_793_);
v___x_807_ = lean_box(0);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v_a_806_);
v___x_808_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(v___f_805_, v___f_802_, v___x_807_, v_a_806_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; 
lean_dec_ref(v___x_808_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1));
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_i_793_, v___x_810_);
v_i_793_ = v___x_811_;
v_b_794_ = v___x_809_;
goto _start;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v_a_790_);
v_a_813_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_808_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_808_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___boxed(lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_as_823_, lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_12270__boxed_830_; size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v___x_12270__boxed_830_ = lean_unbox(v___x_821_);
v_sz_boxed_831_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_832_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(v___x_12270__boxed_830_, v_a_822_, v_as_823_, v_sz_boxed_831_, v_i_boxed_832_, v_b_826_, v___y_827_, v___y_828_);
lean_dec_ref(v_as_823_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(uint8_t v___x_834_, lean_object* v_a_835_, lean_object* v_as_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v_a_835_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_839_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___f_850_; lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_b_839_);
v___x_845_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_846_ = lean_box(0);
v___f_847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0));
v___x_848_ = lean_box(v___x_834_);
v___x_849_ = lean_box(v___x_843_);
lean_inc(v_a_835_);
v___f_850_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed), 11, 5);
lean_closure_set(v___f_850_, 0, v___x_845_);
lean_closure_set(v___f_850_, 1, v___x_848_);
lean_closure_set(v___f_850_, 2, v_a_835_);
lean_closure_set(v___f_850_, 3, v___x_846_);
lean_closure_set(v___f_850_, 4, v___x_849_);
v_a_851_ = lean_array_uget_borrowed(v_as_836_, v_i_838_);
v___x_852_ = lean_box(0);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v_a_851_);
v___x_853_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(v___f_850_, v___f_847_, v___x_852_, v_a_851_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v___x_853_);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__1));
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_add(v_i_838_, v___x_855_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16(v___x_834_, v_a_835_, v_as_836_, v_sz_837_, v___x_856_, v___x_854_, v___y_840_, v___y_841_);
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v_a_835_);
v_a_858_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_853_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_853_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15___boxed(lean_object* v___x_866_, lean_object* v_a_867_, lean_object* v_as_868_, lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v___x_12340__boxed_875_; size_t v_sz_boxed_876_; size_t v_i_boxed_877_; lean_object* v_res_878_; 
v___x_12340__boxed_875_ = lean_unbox(v___x_866_);
v_sz_boxed_876_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_877_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(v___x_12340__boxed_875_, v_a_867_, v_as_868_, v_sz_boxed_876_, v_i_boxed_877_, v_b_871_, v___y_872_, v___y_873_);
lean_dec_ref(v_as_868_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(uint8_t v___x_879_, lean_object* v_a_880_, lean_object* v_inh_881_, lean_object* v_n_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
if (lean_obj_tag(v_n_882_) == 0)
{
lean_object* v_cs_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_921_; 
v_cs_887_ = lean_ctor_get(v_n_882_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_n_882_);
if (v_isSharedCheck_921_ == 0)
{
v___x_889_ = v_n_882_;
v_isShared_890_ = v_isSharedCheck_921_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_cs_887_);
lean_dec(v_n_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_921_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; size_t v_sz_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_b_883_);
v_sz_893_ = lean_array_size(v_cs_887_);
v___x_894_ = ((size_t)0ULL);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(v___x_879_, v_a_880_, v_inh_881_, v_cs_887_, v_sz_893_, v___x_894_, v___x_892_, v___y_884_, v___y_885_);
lean_dec_ref(v_cs_887_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_912_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_912_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_912_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_912_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_fst_900_; 
v_fst_900_ = lean_ctor_get(v_a_896_, 0);
if (lean_obj_tag(v_fst_900_) == 0)
{
lean_object* v_snd_901_; lean_object* v___x_903_; 
v_snd_901_ = lean_ctor_get(v_a_896_, 1);
lean_inc(v_snd_901_);
lean_dec(v_a_896_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v_snd_901_);
v___x_903_ = v___x_889_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_snd_901_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_903_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; 
lean_inc_ref(v_fst_900_);
lean_dec(v_a_896_);
lean_del_object(v___x_889_);
v_val_908_ = lean_ctor_get(v_fst_900_, 0);
lean_inc(v_val_908_);
lean_dec_ref(v_fst_900_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_val_908_);
v___x_910_ = v___x_898_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_908_);
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
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_889_);
v_a_913_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_895_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_895_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_vs_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_956_; 
v_vs_922_ = lean_ctor_get(v_n_882_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_n_882_);
if (v_isSharedCheck_956_ == 0)
{
v___x_924_ = v_n_882_;
v_isShared_925_ = v_isSharedCheck_956_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_vs_922_);
lean_dec(v_n_882_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_956_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; size_t v_sz_928_; size_t v___x_929_; lean_object* v___x_930_; 
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_b_883_);
v_sz_928_ = lean_array_size(v_vs_922_);
v___x_929_ = ((size_t)0ULL);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15(v___x_879_, v_a_880_, v_vs_922_, v_sz_928_, v___x_929_, v___x_927_, v___y_884_, v___y_885_);
lean_dec_ref(v_vs_922_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_fst_935_; 
v_fst_935_ = lean_ctor_get(v_a_931_, 0);
if (lean_obj_tag(v_fst_935_) == 0)
{
lean_object* v_snd_936_; lean_object* v___x_938_; 
v_snd_936_ = lean_ctor_get(v_a_931_, 1);
lean_inc(v_snd_936_);
lean_dec(v_a_931_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_snd_936_);
v___x_938_ = v___x_924_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_snd_936_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_938_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; 
lean_inc_ref(v_fst_935_);
lean_dec(v_a_931_);
lean_del_object(v___x_924_);
v_val_943_ = lean_ctor_get(v_fst_935_, 0);
lean_inc(v_val_943_);
lean_dec_ref(v_fst_935_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_val_943_);
v___x_945_ = v___x_933_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_del_object(v___x_924_);
v_a_948_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_930_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_930_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(uint8_t v___x_957_, lean_object* v_a_958_, lean_object* v_inh_959_, lean_object* v_as_960_, size_t v_sz_961_, size_t v_i_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_lt(v_i_962_, v_sz_961_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_a_958_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v_b_963_);
return v___x_968_;
}
else
{
lean_object* v_snd_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1003_; 
v_snd_969_ = lean_ctor_get(v_b_963_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_963_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_b_963_, 0);
lean_dec(v_unused_1004_);
v___x_971_ = v_b_963_;
v_isShared_972_ = v_isSharedCheck_1003_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_snd_969_);
lean_dec(v_b_963_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1003_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_a_973_; lean_object* v___x_974_; 
v_a_973_ = lean_array_uget_borrowed(v_as_960_, v_i_962_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v_snd_969_);
lean_inc(v_a_973_);
lean_inc(v_a_958_);
v___x_974_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v___x_957_, v_a_958_, v_inh_959_, v_a_973_, v_snd_969_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_994_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_994_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_994_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
if (lean_obj_tag(v_a_975_) == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_a_958_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_a_975_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_979_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_969_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_981_);
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
lean_del_object(v___x_977_);
lean_dec(v_snd_969_);
v_a_986_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v_a_975_);
v___x_987_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v_a_986_);
lean_ctor_set(v___x_971_, 0, v___x_987_);
v___x_989_ = v___x_971_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_986_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_962_, v___x_990_);
v_i_962_ = v___x_991_;
v_b_963_ = v___x_989_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_971_);
lean_dec(v_snd_969_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_a_958_);
v_a_995_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_974_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_974_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14___boxed(lean_object* v___x_1005_, lean_object* v_a_1006_, lean_object* v_inh_1007_, lean_object* v_as_1008_, lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v___x_12400__boxed_1015_; size_t v_sz_boxed_1016_; size_t v_i_boxed_1017_; lean_object* v_res_1018_; 
v___x_12400__boxed_1015_ = lean_unbox(v___x_1005_);
v_sz_boxed_1016_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1017_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__14(v___x_12400__boxed_1015_, v_a_1006_, v_inh_1007_, v_as_1008_, v_sz_boxed_1016_, v_i_boxed_1017_, v_b_1011_, v___y_1012_, v___y_1013_);
lean_dec_ref(v_as_1008_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object* v___x_1019_, lean_object* v_a_1020_, lean_object* v_inh_1021_, lean_object* v_n_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v___x_12421__boxed_1027_; lean_object* v_res_1028_; 
v___x_12421__boxed_1027_ = lean_unbox(v___x_1019_);
v_res_1028_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v___x_12421__boxed_1027_, v_a_1020_, v_inh_1021_, v_n_1022_, v_b_1023_, v___y_1024_, v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(uint8_t v___x_1032_, lean_object* v_a_1033_, lean_object* v_as_1034_, size_t v_sz_1035_, size_t v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_lt(v_i_1036_, v_sz_1035_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v_a_1033_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_b_1037_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_b_1037_);
v___x_1043_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_1044_ = lean_box(0);
v___f_1045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0));
v___x_1046_ = lean_box(v___x_1032_);
v___x_1047_ = lean_box(v___x_1041_);
lean_inc(v_a_1033_);
v___f_1048_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1048_, 0, v___x_1043_);
lean_closure_set(v___f_1048_, 1, v___x_1046_);
lean_closure_set(v___f_1048_, 2, v_a_1033_);
lean_closure_set(v___f_1048_, 3, v___x_1044_);
lean_closure_set(v___f_1048_, 4, v___x_1047_);
v_a_1049_ = lean_array_uget_borrowed(v_as_1034_, v_i_1036_);
v___x_1050_ = lean_box(0);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v_a_1049_);
v___x_1051_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(v___f_1048_, v___f_1045_, v___x_1050_, v_a_1049_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; 
lean_dec_ref(v___x_1051_);
v___x_1052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0));
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1036_, v___x_1053_);
v_i_1036_ = v___x_1054_;
v_b_1037_ = v___x_1052_;
goto _start;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v_a_1033_);
v_a_1056_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1051_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1051_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___boxed(lean_object* v___x_1064_, lean_object* v_a_1065_, lean_object* v_as_1066_, lean_object* v_sz_1067_, lean_object* v_i_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_12639__boxed_1073_; size_t v_sz_boxed_1074_; size_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v___x_12639__boxed_1073_ = lean_unbox(v___x_1064_);
v_sz_boxed_1074_ = lean_unbox_usize(v_sz_1067_);
lean_dec(v_sz_1067_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(v___x_12639__boxed_1073_, v_a_1065_, v_as_1066_, v_sz_boxed_1074_, v_i_boxed_1075_, v_b_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v_as_1066_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(uint8_t v___x_1077_, lean_object* v_a_1078_, lean_object* v_as_1079_, size_t v_sz_1080_, size_t v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_usize_dec_lt(v_i_1081_, v_sz_1080_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_a_1078_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_b_1082_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v_b_1082_);
v___x_1088_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_1089_ = lean_box(0);
v___f_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__15_spec__16___closed__0));
v___x_1091_ = lean_box(v___x_1077_);
v___x_1092_ = lean_box(v___x_1086_);
lean_inc(v_a_1078_);
v___f_1093_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1093_, 0, v___x_1088_);
lean_closure_set(v___f_1093_, 1, v___x_1091_);
lean_closure_set(v___f_1093_, 2, v_a_1078_);
lean_closure_set(v___f_1093_, 3, v___x_1089_);
lean_closure_set(v___f_1093_, 4, v___x_1092_);
v_a_1094_ = lean_array_uget_borrowed(v_as_1079_, v_i_1081_);
v___x_1095_ = lean_box(0);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v_a_1094_);
v___x_1096_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6(v___f_1093_, v___f_1090_, v___x_1095_, v_a_1094_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v___x_1096_);
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17___closed__0));
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1081_, v___x_1098_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11_spec__17(v___x_1077_, v_a_1078_, v_as_1079_, v_sz_1080_, v___x_1099_, v___x_1097_, v___y_1083_, v___y_1084_);
return v___x_1100_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_a_1078_);
v_a_1101_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1096_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1096_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11___boxed(lean_object* v___x_1109_, lean_object* v_a_1110_, lean_object* v_as_1111_, lean_object* v_sz_1112_, lean_object* v_i_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v___x_12707__boxed_1118_; size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v___x_12707__boxed_1118_ = lean_unbox(v___x_1109_);
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1112_);
lean_dec(v_sz_1112_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1113_);
lean_dec(v_i_1113_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(v___x_12707__boxed_1118_, v_a_1110_, v_as_1111_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v_as_1111_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(uint8_t v___x_1122_, lean_object* v_a_1123_, lean_object* v_t_1124_, lean_object* v_init_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_root_1129_; lean_object* v_tail_1130_; lean_object* v___x_1131_; 
v_root_1129_ = lean_ctor_get(v_t_1124_, 0);
lean_inc_ref(v_root_1129_);
v_tail_1130_ = lean_ctor_get(v_t_1124_, 1);
lean_inc_ref(v_tail_1130_);
lean_dec_ref(v_t_1124_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v_a_1123_);
v___x_1131_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v___x_1122_, v_a_1123_, v_init_1125_, v_root_1129_, v_init_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1168_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1168_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1168_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
if (lean_obj_tag(v_a_1132_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; 
lean_dec_ref(v_tail_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_a_1123_);
v_a_1136_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v_a_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
lean_del_object(v___x_1134_);
v_a_1140_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v_a_1132_);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_a_1140_);
v_sz_1143_ = lean_array_size(v_tail_1130_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__11(v___x_1122_, v_a_1123_, v_tail_1130_, v_sz_1143_, v___x_1144_, v___x_1142_, v___y_1126_, v___y_1127_);
lean_dec_ref(v_tail_1130_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1159_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; 
v_fst_1150_ = lean_ctor_get(v_a_1146_, 0);
if (lean_obj_tag(v_fst_1150_) == 0)
{
lean_object* v_snd_1151_; lean_object* v___x_1153_; 
v_snd_1151_ = lean_ctor_get(v_a_1146_, 1);
lean_inc(v_snd_1151_);
lean_dec(v_a_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_snd_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_snd_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1157_; 
lean_inc_ref(v_fst_1150_);
lean_dec(v_a_1146_);
v_val_1155_ = lean_ctor_get(v_fst_1150_, 0);
lean_inc(v_val_1155_);
lean_dec_ref(v_fst_1150_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_val_1155_);
v___x_1157_ = v___x_1148_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_val_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1145_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1145_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_tail_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_a_1123_);
v_a_1169_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1131_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1131_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object* v___x_1177_, lean_object* v_a_1178_, lean_object* v_t_1179_, lean_object* v_init_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v___x_12767__boxed_1184_; lean_object* v_res_1185_; 
v___x_12767__boxed_1184_ = lean_unbox(v___x_1177_);
v_res_1185_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(v___x_12767__boxed_1184_, v_a_1178_, v_t_1179_, v_init_1180_, v___y_1181_, v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(lean_object* v_o_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; lean_object* v___x_1191_; lean_object* v_toEnvExtension_1192_; lean_object* v_asyncMode_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_linterSets_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1189_ = lean_st_ref_get(v___y_1187_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1191_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_toEnvExtension_1192_);
v_asyncMode_1193_ = lean_ctor_get(v_toEnvExtension_1192_, 2);
lean_inc(v_asyncMode_1193_);
lean_dec_ref(v_toEnvExtension_1192_);
v___x_1194_ = lean_box(1);
v___x_1195_ = lean_box(0);
v_linterSets_1196_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1194_, v___x_1191_, v_env_1190_, v_asyncMode_1193_, v___x_1195_);
lean_dec(v_asyncMode_1193_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_o_1186_);
lean_ctor_set(v___x_1197_, 1, v_linterSets_1196_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1199_, v___y_1200_);
lean_dec(v___y_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v_scopes_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_opts_1210_; lean_object* v___x_1211_; 
v___x_1206_ = lean_st_ref_get(v___y_1204_);
v_scopes_1207_ = lean_ctor_get(v___x_1206_, 2);
lean_inc(v_scopes_1207_);
lean_dec(v___x_1206_);
v___x_1208_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1209_ = l_List_head_x21___redArg(v___x_1208_, v_scopes_1207_);
lean_dec(v_scopes_1207_);
v_opts_1210_ = lean_ctor_get(v___x_1209_, 1);
lean_inc_ref(v_opts_1210_);
lean_dec(v___x_1209_);
v___x_1211_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_opts_1210_, v___y_1204_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0(lean_object* v_x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1220_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1218_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1217_, v___y_1218_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1218_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_1227_ = l_Lean_Linter_getLinterValue(v___x_1226_, v_a_1223_);
lean_dec(v_a_1223_);
v___x_1228_ = lean_box(0);
v___x_1229_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__7(v___x_1227_, v_a_1221_, v_a_1225_, v___x_1228_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1237_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1228_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1228_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0___boxed(lean_object* v_x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_1238_, v___y_1239_, v___y_1240_);
lean_dec(v_x_1238_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object* v_o_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1254_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object* v_o_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5(uint8_t v___x_1264_, lean_object* v_i_1265_, lean_object* v_a_1266_, lean_object* v_as_1267_, lean_object* v_as_x27_1268_, lean_object* v_b_1269_, lean_object* v_a_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___redArg(v___x_1264_, v_i_1265_, v_a_1266_, v_as_x27_1268_, v_b_1269_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object* v___x_1275_, lean_object* v_i_1276_, lean_object* v_a_1277_, lean_object* v_as_1278_, lean_object* v_as_x27_1279_, lean_object* v_b_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_13002__boxed_1285_; lean_object* v_res_1286_; 
v___x_13002__boxed_1285_ = lean_unbox(v___x_1275_);
v_res_1286_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__5(v___x_13002__boxed_1285_, v_i_1276_, v_a_1277_, v_as_1278_, v_as_x27_1279_, v_b_1280_, v_a_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec(v_as_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_i_1276_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6(lean_object* v_msgData_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___redArg(v_msgData_1287_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6___boxed(lean_object* v_msgData_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_spec__6(v_msgData_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_1297_, lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___redArg(v_msg_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__10(v_00_u03b1_1303_, v_msg_1304_, v___y_1305_, v___y_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8(lean_object* v_00_u03b1_1309_, lean_object* v_preNode_1310_, lean_object* v_postNode_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___redArg(v_preNode_1310_, v_postNode_1311_, v_x_1312_, v_x_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_preNode_1319_, lean_object* v_postNode_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8(v_00_u03b1_1318_, v_preNode_1319_, v_postNode_1320_, v_x_1321_, v_x_1322_, v___y_1323_, v___y_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11(lean_object* v_00_u03b1_1327_, lean_object* v_preNode_1328_, lean_object* v_postNode_1329_, lean_object* v___x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___redArg(v_preNode_1328_, v_postNode_1329_, v___x_1330_, v_x_1331_, v_x_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_preNode_1338_, lean_object* v_postNode_1339_, lean_object* v___x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__6_spec__8_spec__11(v_00_u03b1_1337_, v_preNode_1338_, v_postNode_1339_, v___x_1340_, v_x_1341_, v_x_1342_, v___y_1343_, v___y_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_Linter_Coe_coeLinter));
v___x_1349_ = l_Lean_Elab_Command_addLinter(v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
return v_res_1351_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Coe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Coe_linter_deprecatedCoercions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Coe_linter_deprecatedCoercions);
lean_dec_ref(res);
res = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Coe(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Coe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Coe(builtin);
}
#ifdef __cplusplus
}
#endif
