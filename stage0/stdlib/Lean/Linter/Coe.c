// Lean compiler output
// Module: Lean.Linter.Coe
// Imports: public import Lean.Elab.Command public import Lean.Server.InfoUtils import Lean.Linter.Init import all Lean.Elab.Term.TermElabM
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedCoercions"};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(225, 120, 31, 12, 27, 111, 143, 243)}};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Validate that no deprecated coercions are used."};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__3_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Coe"};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(104, 245, 251, 188, 163, 69, 36, 187)}};
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__0_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(21, 194, 173, 54, 161, 152, 189, 121)}};
static const lean_ctor_object l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__1_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 196, 227, 214, 191, 242, 190, 69)}};
static const lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "This term uses the deprecated coercion `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "This term uses the coercion `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, which is banned in Lean's core library."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__10_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linterCoe"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__11_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 173, 243, 24, 185, 201, 144)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(185, 49, 173, 29, 145, 193, 214, 13)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12_value;
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__19 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__5_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__6_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__7_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(104, 245, 251, 188, 163, 69, 36, 187)}};
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value_aux_2),((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 112, 251, 217, 194, 245, 186, 89)}};
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Coe_coeLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__0_value),((lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__2_value)}};
static const lean_object* l_Lean_Linter_Coe_coeLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Coe_coeLinter = (const lean_object*)&l_Lean_Linter_Coe_coeLinter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = ((lean_object*)(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__2_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_23_ = ((lean_object*)(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__4_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_24_ = ((lean_object*)(l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn___closed__8_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_));
v___x_25_ = l_Lean_Option_register___at___00__private_Lean_Elab_Term_TermElabM_0__Lean_Elab_Term_initFn_00___x40_Lean_Elab_Term_TermElabM_3465893884____hygCtx___hyg_4__spec__0(v___x_22_, v___x_23_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(lean_object* v_toPure_28_, lean_object* v_____do__lift_29_){
_start:
{
lean_object* v___x_30_; lean_object* v_name_31_; lean_object* v_map_32_; uint8_t v___x_33_; lean_object* v___x_34_; 
v___x_30_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v_name_31_ = lean_ctor_get(v___x_30_, 0);
v_map_32_ = lean_ctor_get(v_____do__lift_29_, 0);
v___x_33_ = 1;
v___x_34_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_32_, v_name_31_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(v___x_33_);
v___x_36_ = lean_apply_2(v_toPure_28_, lean_box(0), v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v___x_34_, 1);
if (lean_obj_tag(v_val_37_) == 1)
{
uint8_t v_v_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_v_38_ = lean_ctor_get_uint8(v_val_37_, 0);
lean_dec_ref_known(v_val_37_, 0);
v___x_39_ = lean_box(v_v_38_);
v___x_40_ = lean_apply_2(v_toPure_28_, lean_box(0), v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_val_37_);
v___x_41_ = lean_box(v___x_33_);
v___x_42_ = lean_apply_2(v_toPure_28_, lean_box(0), v___x_41_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed(lean_object* v_toPure_43_, lean_object* v_____do__lift_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(v_toPure_43_, v_____do__lift_44_);
lean_dec_ref(v_____do__lift_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_toPure_50_; lean_object* v___f_51_; lean_object* v___x_52_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toApplicative_48_);
v_toBind_49_ = lean_ctor_get(v_inst_46_, 1);
lean_inc(v_toBind_49_);
lean_dec_ref(v_inst_46_);
v_toPure_50_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc(v_toPure_50_);
lean_dec_ref(v_toApplicative_48_);
v___f_51_ = lean_alloc_closure((void*)(l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_51_, 0, v_toPure_50_);
v___x_52_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v_inst_47_, v___f_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(lean_object* v_m_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(v_inst_54_, v_inst_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v_env_73_; lean_object* v___x_74_; lean_object* v_mainModule_75_; lean_object* v___x_76_; 
v___x_72_ = lean_st_ref_get(v___y_70_);
v_env_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_env_73_);
lean_dec(v___x_72_);
v___x_74_ = l_Lean_Environment_header(v_env_73_);
lean_dec_ref(v_env_73_);
v_mainModule_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_mainModule_75_);
lean_dec_ref(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v_mainModule_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_77_);
lean_dec(v___y_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_infoState_91_; lean_object* v_trees_92_; lean_object* v___x_93_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_infoState_91_ = lean_ctor_get(v___x_90_, 8);
lean_inc_ref(v_infoState_91_);
lean_dec(v___x_90_);
v_trees_92_ = lean_ctor_get(v_infoState_91_, 2);
lean_inc_ref(v_trees_92_);
lean_dec_ref(v_infoState_91_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_trees_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_94_);
lean_dec(v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_104_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_instMonadEIO(lean_box(0));
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_toApplicative_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_145_; 
v___x_112_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0);
v___x_113_ = l_StateRefT_x27_instMonad___redArg(v___x_112_);
v_toApplicative_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_113_, 1);
lean_dec(v_unused_146_);
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_145_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_toApplicative_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_145_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_toFunctor_118_; lean_object* v_toSeq_119_; lean_object* v_toSeqLeft_120_; lean_object* v_toSeqRight_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_143_; 
v_toFunctor_118_ = lean_ctor_get(v_toApplicative_114_, 0);
v_toSeq_119_ = lean_ctor_get(v_toApplicative_114_, 2);
v_toSeqLeft_120_ = lean_ctor_get(v_toApplicative_114_, 3);
v_toSeqRight_121_ = lean_ctor_get(v_toApplicative_114_, 4);
v_isSharedCheck_143_ = !lean_is_exclusive(v_toApplicative_114_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_dec(v_unused_144_);
v___x_123_ = v_toApplicative_114_;
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_toSeqRight_121_);
lean_inc(v_toSeqLeft_120_);
lean_inc(v_toSeq_119_);
lean_inc(v_toFunctor_118_);
lean_dec(v_toApplicative_114_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___f_125_; lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_134_; 
v___f_125_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1));
v___f_126_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2));
lean_inc_ref(v_toFunctor_118_);
v___f_127_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_127_, 0, v_toFunctor_118_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_128_, 0, v_toFunctor_118_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___f_127_);
lean_ctor_set(v___x_129_, 1, v___f_128_);
v___f_130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_130_, 0, v_toSeqRight_121_);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_131_, 0, v_toSeqLeft_120_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_132_, 0, v_toSeq_119_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 4, v___f_130_);
lean_ctor_set(v___x_123_, 3, v___f_131_);
lean_ctor_set(v___x_123_, 2, v___f_132_);
lean_ctor_set(v___x_123_, 1, v___f_125_);
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_134_ = v___x_123_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___f_125_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v___f_132_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v___f_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___f_130_);
v___x_134_ = v_reuseFailAlloc_142_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___f_126_);
lean_ctor_set(v___x_116_, 0, v___x_134_);
v___x_136_ = v___x_116_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___f_126_);
v___x_136_ = v_reuseFailAlloc_141_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_8328__overap_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(0);
v___x_138_ = l_instInhabitedOfMonad___redArg(v___x_136_, v___x_137_);
v___x_8328__overap_139_ = lean_panic_fn_borrowed(v___x_138_, v_msg_108_);
lean_dec(v___x_138_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
v___x_140_ = lean_apply_3(v___x_8328__overap_139_, v___y_109_, v___y_110_, lean_box(0));
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_151_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2));
v___x_156_ = lean_unsigned_to_nat(21u);
v___x_157_ = lean_unsigned_to_nat(65u);
v___x_158_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1));
v___x_159_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0));
v___x_160_ = l_mkPanicMessageWithDecl(v___x_159_, v___x_158_, v___x_157_, v___x_156_, v___x_155_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(lean_object* v_preNode_161_, lean_object* v_postNode_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
switch(lean_obj_tag(v_x_164_))
{
case 0:
{
lean_object* v_i_168_; lean_object* v_t_169_; lean_object* v___x_170_; 
v_i_168_ = lean_ctor_get(v_x_164_, 0);
lean_inc_ref(v_i_168_);
v_t_169_ = lean_ctor_get(v_x_164_, 1);
lean_inc_ref(v_t_169_);
lean_dec_ref_known(v_x_164_, 2);
v___x_170_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_168_, v_x_163_);
v_x_163_ = v___x_170_;
v_x_164_ = v_t_169_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref_known(v_x_164_, 2);
lean_dec_ref(v_postNode_162_);
lean_dec_ref(v_preNode_161_);
v___x_172_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3);
v___x_173_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v___x_172_, v___y_165_, v___y_166_);
return v___x_173_;
}
else
{
lean_object* v_i_174_; lean_object* v_children_175_; lean_object* v_val_176_; lean_object* v___x_177_; 
v_i_174_ = lean_ctor_get(v_x_164_, 0);
lean_inc_ref_n(v_i_174_, 2);
v_children_175_ = lean_ctor_get(v_x_164_, 1);
lean_inc_ref_n(v_children_175_, 2);
lean_dec_ref_known(v_x_164_, 2);
v_val_176_ = lean_ctor_get(v_x_163_, 0);
lean_inc_n(v_val_176_, 2);
lean_inc_ref(v_preNode_161_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
v___x_177_ = lean_apply_6(v_preNode_161_, v_val_176_, v_i_174_, v_children_175_, v___y_165_, v___y_166_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; uint8_t v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = lean_unbox(v_a_178_);
lean_dec(v_a_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_preNode_161_);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_x_163_, 0);
lean_dec(v_unused_205_);
v___x_181_ = v_x_163_;
v_isShared_182_ = v_isSharedCheck_204_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_x_163_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_204_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(0);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
v___x_184_ = lean_apply_7(v_postNode_162_, v_val_176_, v_i_174_, v_children_175_, v___x_183_, v___y_165_, v___y_166_, lean_box(0));
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_195_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_195_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v_a_185_);
v___x_190_ = v___x_181_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_del_object(v___x_181_);
v_a_196_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_184_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_184_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = l_Lean_Elab_Info_updateContext_x3f(v_x_163_, v_i_174_);
v___x_207_ = l_Lean_PersistentArray_toList___redArg(v_children_175_);
v___x_208_ = lean_box(0);
lean_inc_ref(v_postNode_162_);
v___x_209_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_161_, v_postNode_162_, v___x_206_, v___x_207_, v___x_208_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
v___x_211_ = lean_apply_7(v_postNode_162_, v_val_176_, v_i_174_, v_children_175_, v_a_210_, v___y_165_, v___y_166_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_val_176_);
lean_dec_ref(v_children_175_);
lean_dec_ref(v_i_174_);
lean_dec_ref(v_postNode_162_);
v_a_229_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_209_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_209_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_val_176_);
lean_dec_ref(v_children_175_);
lean_dec_ref_known(v_x_163_, 1);
lean_dec_ref(v_i_174_);
lean_dec_ref(v_postNode_162_);
lean_dec_ref(v_preNode_161_);
v_a_237_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_177_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_177_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
default: 
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_x_163_);
lean_dec_ref(v_postNode_162_);
lean_dec_ref(v_preNode_161_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_x_164_, 0);
lean_dec(v_unused_253_);
v___x_246_ = v_x_164_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_dec(v_x_164_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(lean_object* v_preNode_254_, lean_object* v_postNode_255_, lean_object* v___x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v___x_256_);
lean_dec_ref(v_postNode_255_);
lean_dec_ref(v_preNode_254_);
v___x_262_ = l_List_reverse___redArg(v_x_258_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_283_; 
v_head_264_ = lean_ctor_get(v_x_257_, 0);
v_tail_265_ = lean_ctor_get(v_x_257_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_283_ == 0)
{
v___x_267_ = v_x_257_;
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_tail_265_);
lean_inc(v_head_264_);
lean_dec(v_x_257_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; 
lean_inc(v___x_256_);
lean_inc_ref(v_postNode_255_);
lean_inc_ref(v_preNode_254_);
v___x_269_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_254_, v_postNode_255_, v___x_256_, v_head_264_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_x_258_);
lean_ctor_set(v___x_267_, 0, v_a_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_258_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_x_257_ = v_tail_265_;
v_x_258_ = v___x_272_;
goto _start;
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_del_object(v___x_267_);
lean_dec(v_tail_265_);
lean_dec(v_x_258_);
lean_dec(v___x_256_);
lean_dec_ref(v_postNode_255_);
lean_dec_ref(v_preNode_254_);
v_a_275_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_269_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_269_);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_preNode_284_, lean_object* v_postNode_285_, lean_object* v___x_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_284_, v_postNode_285_, v___x_286_, v_x_287_, v_x_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___boxed(lean_object* v_preNode_293_, lean_object* v_postNode_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_293_, v_postNode_294_, v_x_295_, v_x_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(lean_object* v_postNode_301_, lean_object* v_ci_302_, lean_object* v_i_303_, lean_object* v_cs_304_, lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_309_ = lean_apply_6(v_postNode_301_, v_ci_302_, v_i_303_, v_cs_304_, v___y_306_, v___y_307_, lean_box(0));
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed(lean_object* v_postNode_310_, lean_object* v_ci_311_, lean_object* v_i_312_, lean_object* v_cs_313_, lean_object* v_x_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(v_postNode_310_, v_ci_311_, v_i_312_, v_cs_313_, v_x_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v_x_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(lean_object* v_preNode_319_, lean_object* v_postNode_320_, lean_object* v_ctx_x3f_321_, lean_object* v_t_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(v___f_326_, 0, v_postNode_320_);
v___x_327_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_319_, v___f_326_, v_ctx_x3f_321_, v_t_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v___x_327_, 0);
lean_dec(v_unused_336_);
v___x_329_ = v___x_327_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_dec(v___x_327_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_box(0);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_327_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_327_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object* v_preNode_345_, lean_object* v_postNode_346_, lean_object* v_ctx_x3f_347_, lean_object* v_t_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v_preNode_345_, v_postNode_346_, v_ctx_x3f_347_, v_t_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_ctor_set(v___x_358_, 3, v___x_357_);
lean_ctor_set(v___x_358_, 4, v___x_356_);
lean_ctor_set(v___x_358_, 5, v___x_356_);
lean_ctor_set(v___x_358_, 6, v___x_356_);
lean_ctor_set(v___x_358_, 7, v___x_356_);
lean_ctor_set(v___x_358_, 8, v___x_356_);
lean_ctor_set(v___x_358_, 9, v___x_356_);
lean_ctor_set(v___x_358_, 10, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_unsigned_to_nat(32u);
v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_362_ = ((size_t)5ULL);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_unsigned_to_nat(32u);
v___x_365_ = lean_mk_empty_array_with_capacity(v___x_364_);
v___x_366_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3);
v___x_367_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
lean_ctor_set(v___x_367_, 2, v___x_363_);
lean_ctor_set(v___x_367_, 3, v___x_363_);
lean_ctor_set_usize(v___x_367_, 4, v___x_362_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_368_ = lean_box(1);
v___x_369_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4);
v___x_370_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
lean_ctor_set(v___x_371_, 2, v___x_368_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(lean_object* v_msgData_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; lean_object* v___x_377_; lean_object* v_scopes_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_opts_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_375_ = lean_st_ref_get(v___y_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___x_377_ = lean_st_ref_get(v___y_373_);
v_scopes_378_ = lean_ctor_get(v___x_377_, 2);
lean_inc(v_scopes_378_);
lean_dec(v___x_377_);
v___x_379_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_380_ = l_List_head_x21___redArg(v___x_379_, v_scopes_378_);
lean_dec(v_scopes_378_);
v_opts_381_ = lean_ctor_get(v___x_380_, 1);
lean_inc_ref(v_opts_381_);
lean_dec(v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2);
v___x_383_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5);
v___x_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_384_, 0, v_env_376_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v_opts_381_);
v___x_385_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_msgData_372_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_387_, v___y_388_);
lean_dec(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(uint8_t v_suppressElabErrors_392_, uint8_t v___y_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 1)
{
lean_object* v_pre_395_; 
v_pre_395_ = lean_ctor_get(v_x_394_, 0);
if (lean_obj_tag(v_pre_395_) == 0)
{
lean_object* v_str_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_str_396_ = lean_ctor_get(v_x_394_, 1);
v___x_397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0));
v___x_398_ = lean_string_dec_eq(v_str_396_, v___x_397_);
if (v___x_398_ == 0)
{
return v___x_398_;
}
else
{
return v_suppressElabErrors_392_;
}
}
else
{
return v___y_393_;
}
}
else
{
return v___y_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_399_, lean_object* v___y_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_suppressElabErrors_boxed_402_; uint8_t v___y_10520__boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_suppressElabErrors_boxed_402_ = lean_unbox(v_suppressElabErrors_399_);
v___y_10520__boxed_403_ = lean_unbox(v___y_400_);
v_res_404_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(v_suppressElabErrors_boxed_402_, v___y_10520__boxed_403_, v_x_401_);
lean_dec(v_x_401_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(lean_object* v_ref_407_, lean_object* v_msgData_408_, uint8_t v_severity_409_, uint8_t v_isSilent_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; lean_object* v___y_422_; uint8_t v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; uint8_t v___y_507_; uint8_t v___y_508_; lean_object* v___y_509_; uint8_t v___y_510_; lean_object* v___y_511_; uint8_t v___y_515_; uint8_t v___y_516_; uint8_t v___y_517_; uint8_t v___x_532_; uint8_t v___y_534_; uint8_t v___y_535_; uint8_t v___y_536_; uint8_t v___y_538_; uint8_t v___x_550_; 
v___x_532_ = 2;
v___x_550_ = l_Lean_instBEqMessageSeverity_beq(v_severity_409_, v___x_532_);
if (v___x_550_ == 0)
{
v___y_538_ = v___x_550_;
goto v___jp_537_;
}
else
{
uint8_t v___x_551_; 
lean_inc_ref(v_msgData_408_);
v___x_551_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_408_);
v___y_538_ = v___x_551_;
goto v___jp_537_;
}
v___jp_414_:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_Command_getScope___redArg(v___y_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lean_Elab_Command_getScope___redArg(v___y_422_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_461_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_461_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_461_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_461_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v_currNamespace_431_; lean_object* v_openDecls_432_; lean_object* v_env_433_; lean_object* v_messages_434_; lean_object* v_scopes_435_; lean_object* v_usedQuotCtxts_436_; lean_object* v_nextMacroScope_437_; lean_object* v_maxRecDepth_438_; lean_object* v_ngen_439_; lean_object* v_auxDeclNGen_440_; lean_object* v_infoState_441_; lean_object* v_traceState_442_; lean_object* v_snapshotTasks_443_; lean_object* v_prevLinterStates_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_460_; 
v___x_430_ = lean_st_ref_take(v___y_422_);
v_currNamespace_431_ = lean_ctor_get(v_a_424_, 2);
lean_inc(v_currNamespace_431_);
lean_dec(v_a_424_);
v_openDecls_432_ = lean_ctor_get(v_a_426_, 3);
lean_inc(v_openDecls_432_);
lean_dec(v_a_426_);
v_env_433_ = lean_ctor_get(v___x_430_, 0);
v_messages_434_ = lean_ctor_get(v___x_430_, 1);
v_scopes_435_ = lean_ctor_get(v___x_430_, 2);
v_usedQuotCtxts_436_ = lean_ctor_get(v___x_430_, 3);
v_nextMacroScope_437_ = lean_ctor_get(v___x_430_, 4);
v_maxRecDepth_438_ = lean_ctor_get(v___x_430_, 5);
v_ngen_439_ = lean_ctor_get(v___x_430_, 6);
v_auxDeclNGen_440_ = lean_ctor_get(v___x_430_, 7);
v_infoState_441_ = lean_ctor_get(v___x_430_, 8);
v_traceState_442_ = lean_ctor_get(v___x_430_, 9);
v_snapshotTasks_443_ = lean_ctor_get(v___x_430_, 10);
v_prevLinterStates_444_ = lean_ctor_get(v___x_430_, 11);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_460_ == 0)
{
v___x_446_ = v___x_430_;
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_prevLinterStates_444_);
lean_inc(v_snapshotTasks_443_);
lean_inc(v_traceState_442_);
lean_inc(v_infoState_441_);
lean_inc(v_auxDeclNGen_440_);
lean_inc(v_ngen_439_);
lean_inc(v_maxRecDepth_438_);
lean_inc(v_nextMacroScope_437_);
lean_inc(v_usedQuotCtxts_436_);
lean_inc(v_scopes_435_);
lean_inc(v_messages_434_);
lean_inc(v_env_433_);
lean_dec(v___x_430_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_currNamespace_431_);
lean_ctor_set(v___x_448_, 1, v_openDecls_432_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___y_415_);
lean_inc_ref(v___y_417_);
lean_inc_ref(v___y_420_);
v___x_450_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_450_, 0, v___y_420_);
lean_ctor_set(v___x_450_, 1, v___y_419_);
lean_ctor_set(v___x_450_, 2, v___y_418_);
lean_ctor_set(v___x_450_, 3, v___y_417_);
lean_ctor_set(v___x_450_, 4, v___x_449_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5, v___y_421_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 1, v___y_416_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 2, v_isSilent_410_);
v___x_451_ = l_Lean_MessageLog_add(v___x_450_, v_messages_434_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_451_);
v___x_453_ = v___x_446_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_env_433_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_scopes_435_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_usedQuotCtxts_436_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_nextMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_459_, 5, v_maxRecDepth_438_);
lean_ctor_set(v_reuseFailAlloc_459_, 6, v_ngen_439_);
lean_ctor_set(v_reuseFailAlloc_459_, 7, v_auxDeclNGen_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 8, v_infoState_441_);
lean_ctor_set(v_reuseFailAlloc_459_, 9, v_traceState_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 10, v_snapshotTasks_443_);
lean_ctor_set(v_reuseFailAlloc_459_, 11, v_prevLinterStates_444_);
v___x_453_ = v_reuseFailAlloc_459_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_454_ = lean_st_ref_put(v___y_422_, v___x_453_);
v___x_455_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_455_);
v___x_457_ = v___x_428_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_a_424_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_415_);
v_a_462_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_425_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_425_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_415_);
v_a_470_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_423_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_423_);
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
}
v___jp_478_:
{
lean_object* v_fileName_484_; lean_object* v_fileMap_485_; uint8_t v_suppressElabErrors_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_505_; 
v_fileName_484_ = lean_ctor_get(v___y_411_, 0);
v_fileMap_485_ = lean_ctor_get(v___y_411_, 1);
v_suppressElabErrors_486_ = lean_ctor_get_uint8(v___y_411_, sizeof(void*)*10);
v___x_487_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_408_);
v___x_488_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v___x_487_, v___y_412_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref_n(v_fileMap_485_, 2);
v___x_493_ = l_Lean_FileMap_toPosition(v_fileMap_485_, v___y_480_);
lean_dec(v___y_480_);
v___x_494_ = l_Lean_FileMap_toPosition(v_fileMap_485_, v___y_483_);
lean_dec(v___y_483_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
v___x_496_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0));
if (v_suppressElabErrors_486_ == 0)
{
lean_del_object(v___x_491_);
v___y_415_ = v_a_489_;
v___y_416_ = v___y_481_;
v___y_417_ = v___x_496_;
v___y_418_ = v___x_495_;
v___y_419_ = v___x_493_;
v___y_420_ = v_fileName_484_;
v___y_421_ = v___y_482_;
v___y_422_ = v___y_412_;
goto v___jp_414_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___f_499_; uint8_t v___x_500_; 
v___x_497_ = lean_box(v_suppressElabErrors_486_);
v___x_498_ = lean_box(v___y_479_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_499_, 0, v___x_497_);
lean_closure_set(v___f_499_, 1, v___x_498_);
lean_inc(v_a_489_);
v___x_500_ = l_Lean_MessageData_hasTag(v___f_499_, v_a_489_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec_ref_known(v___x_495_, 1);
lean_dec_ref(v___x_493_);
lean_dec(v_a_489_);
v___x_501_ = lean_box(0);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_501_);
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_del_object(v___x_491_);
v___y_415_ = v_a_489_;
v___y_416_ = v___y_481_;
v___y_417_ = v___x_496_;
v___y_418_ = v___x_495_;
v___y_419_ = v___x_493_;
v___y_420_ = v_fileName_484_;
v___y_421_ = v___y_482_;
v___y_422_ = v___y_412_;
goto v___jp_414_;
}
}
}
}
v___jp_506_:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Syntax_getTailPos_x3f(v___y_509_, v___y_510_);
lean_dec(v___y_509_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_inc(v___y_511_);
v___y_479_ = v___y_507_;
v___y_480_ = v___y_511_;
v___y_481_ = v___y_508_;
v___y_482_ = v___y_510_;
v___y_483_ = v___y_511_;
goto v___jp_478_;
}
else
{
lean_object* v_val_513_; 
v_val_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v___x_512_, 1);
v___y_479_ = v___y_507_;
v___y_480_ = v___y_511_;
v___y_481_ = v___y_508_;
v___y_482_ = v___y_510_;
v___y_483_ = v_val_513_;
goto v___jp_478_;
}
}
v___jp_514_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Elab_Command_getRef___redArg(v___y_411_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_ref_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_ref_520_ = l_Lean_replaceRef(v_ref_407_, v_a_519_);
lean_dec(v_a_519_);
v___x_521_ = l_Lean_Syntax_getPos_x3f(v_ref_520_, v___y_516_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___y_507_ = v___y_515_;
v___y_508_ = v___y_517_;
v___y_509_ = v_ref_520_;
v___y_510_ = v___y_516_;
v___y_511_ = v___x_522_;
goto v___jp_506_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_521_, 1);
v___y_507_ = v___y_515_;
v___y_508_ = v___y_517_;
v___y_509_ = v_ref_520_;
v___y_510_ = v___y_516_;
v___y_511_ = v_val_523_;
goto v___jp_506_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v_msgData_408_);
v_a_524_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_518_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_518_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
v___jp_533_:
{
if (v___y_536_ == 0)
{
v___y_515_ = v___y_534_;
v___y_516_ = v___y_535_;
v___y_517_ = v_severity_409_;
goto v___jp_514_;
}
else
{
v___y_515_ = v___y_534_;
v___y_516_ = v___y_535_;
v___y_517_ = v___x_532_;
goto v___jp_514_;
}
}
v___jp_537_:
{
if (v___y_538_ == 0)
{
lean_object* v___x_539_; lean_object* v_scopes_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_opts_543_; uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_539_ = lean_st_ref_get(v___y_412_);
v_scopes_540_ = lean_ctor_get(v___x_539_, 2);
lean_inc(v_scopes_540_);
lean_dec(v___x_539_);
v___x_541_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_542_ = l_List_head_x21___redArg(v___x_541_, v_scopes_540_);
lean_dec(v_scopes_540_);
v_opts_543_ = lean_ctor_get(v___x_542_, 1);
lean_inc_ref(v_opts_543_);
lean_dec(v___x_542_);
v___x_544_ = 1;
v___x_545_ = l_Lean_instBEqMessageSeverity_beq(v_severity_409_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec_ref(v_opts_543_);
v___y_534_ = v___y_538_;
v___y_535_ = v___y_538_;
v___y_536_ = v___x_545_;
goto v___jp_533_;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = l_Lean_warningAsError;
v___x_547_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(v_opts_543_, v___x_546_);
lean_dec_ref(v_opts_543_);
v___y_534_ = v___y_538_;
v___y_535_ = v___y_538_;
v___y_536_ = v___x_547_;
goto v___jp_533_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_msgData_408_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___boxed(lean_object* v_ref_552_, lean_object* v_msgData_553_, lean_object* v_severity_554_, lean_object* v_isSilent_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_severity_boxed_559_; uint8_t v_isSilent_boxed_560_; lean_object* v_res_561_; 
v_severity_boxed_559_ = lean_unbox(v_severity_554_);
v_isSilent_boxed_560_ = lean_unbox(v_isSilent_555_);
v_res_561_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_552_, v_msgData_553_, v_severity_boxed_559_, v_isSilent_boxed_560_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v_ref_552_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(lean_object* v_ref_562_, lean_object* v_msgData_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = 1;
v___x_568_ = 0;
v___x_569_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_562_, v_msgData_563_, v___x_567_, v___x_568_, v___y_564_, v___y_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object* v_ref_570_, lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_ref_570_, v_msgData_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v_ref_570_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(lean_object* v_linterOption_582_, lean_object* v_stx_583_, lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_name_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_606_; 
v_name_588_ = lean_ctor_get(v_linterOption_582_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_linterOption_582_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_linterOption_582_, 1);
lean_dec(v_unused_607_);
v___x_590_ = v_linterOption_582_;
v_isShared_591_ = v_isSharedCheck_606_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_name_588_);
lean_dec(v_linterOption_582_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_606_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_592_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1);
lean_inc(v_name_588_);
v___x_593_ = l_Lean_MessageData_ofName(v_name_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 7);
lean_ctor_set(v___x_590_, 1, v___x_593_);
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_605_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_disable_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_596_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v_disable_598_ = l_Lean_MessageData_note(v___x_597_);
v___x_599_ = l_Lean_Linter_linterMessageTag;
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v_msg_584_);
lean_ctor_set(v___x_600_, 1, v_disable_598_);
v___x_601_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_602_, 0, v_name_588_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v_stx_583_);
v___x_603_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_603_, 0, v_stx_583_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_583_, v___x_603_, v___y_585_, v___y_586_);
lean_dec(v_stx_583_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(lean_object* v_linterOption_608_, lean_object* v_stx_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v_linterOption_608_, v_stx_609_, v_msg_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object* v_a_615_, lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_array_uget_borrowed(v_as_616_, v_i_617_);
v___x_621_ = lean_name_eq(v_a_615_, v___x_620_);
if (v___x_621_ == 0)
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_617_, v___x_622_);
v_i_617_ = v___x_623_;
goto _start;
}
else
{
return v___x_621_;
}
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object* v_a_626_, lean_object* v_as_627_, lean_object* v_i_628_, lean_object* v_stop_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_629_);
lean_dec(v_stop_629_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_626_, v_as_627_, v_i_boxed_630_, v_stop_boxed_631_);
lean_dec_ref(v_as_627_);
lean_dec(v_a_626_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object* v_as_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_array_get_size(v_as_634_);
v___x_638_ = lean_nat_dec_lt(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
return v___x_638_;
}
else
{
if (v___x_638_ == 0)
{
return v___x_638_;
}
else
{
size_t v___x_639_; size_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_637_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_635_, v_as_634_, v___x_639_, v___x_640_);
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object* v_as_642_, lean_object* v_a_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v_as_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_as_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(uint8_t v___x_681_, lean_object* v_i_682_, lean_object* v_a_683_, lean_object* v_as_x27_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
if (lean_obj_tag(v_as_x27_684_) == 0)
{
lean_object* v___x_689_; 
lean_dec_ref(v_i_682_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_b_685_);
return v___x_689_;
}
else
{
lean_object* v_head_690_; lean_object* v_tail_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___y_696_; lean_object* v___y_697_; uint8_t v___y_715_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_head_690_ = lean_ctor_get(v_as_x27_684_, 0);
v_tail_691_ = lean_ctor_get(v_as_x27_684_, 1);
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_694_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12));
v___x_726_ = lean_name_eq(v_a_683_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13));
v___x_728_ = l_Lean_Name_getRoot(v_a_683_);
v___x_729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__19));
v___x_730_ = l_List_elem___redArg(v___x_727_, v___x_728_, v___x_729_);
v___y_715_ = v___x_730_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___x_726_;
goto v___jp_714_;
}
v___jp_695_:
{
if (v___x_681_ == 0)
{
v_as_x27_684_ = v_tail_691_;
v_b_685_ = v___x_692_;
goto _start;
}
else
{
lean_object* v___x_699_; lean_object* v_env_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_st_ref_get(v___y_697_);
v_env_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_700_);
lean_dec(v___x_699_);
v___x_701_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_head_690_);
v___x_702_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_693_, v___x_701_, v_env_700_, v_head_690_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v_stx_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref_known(v___x_702_, 1);
v_stx_703_ = lean_ctor_get(v_i_682_, 0);
v___x_704_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1));
v___x_705_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3);
lean_inc(v_head_690_);
v___x_706_ = l_Lean_MessageData_ofConstName(v_head_690_, v___x_681_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_704_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
lean_inc(v_stx_703_);
v___x_711_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v___x_694_, v_stx_703_, v___x_710_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_dec_ref_known(v___x_711_, 1);
v_as_x27_684_ = v_tail_691_;
v_b_685_ = v___x_692_;
goto _start;
}
else
{
lean_dec_ref(v_i_682_);
return v___x_711_;
}
}
else
{
lean_dec(v___x_702_);
v_as_x27_684_ = v_tail_691_;
v_b_685_ = v___x_692_;
goto _start;
}
}
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
v___y_696_ = v___y_686_;
v___y_697_ = v___y_687_;
goto v___jp_695_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Linter_Coe_coercionsBannedInCore));
v___x_717_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v___x_716_, v_head_690_);
if (v___x_717_ == 0)
{
v___y_696_ = v___y_686_;
v___y_697_ = v___y_687_;
goto v___jp_695_;
}
else
{
lean_object* v_stx_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_stx_718_ = lean_ctor_get(v_i_682_, 0);
v___x_719_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7);
lean_inc(v_head_690_);
v___x_720_ = l_Lean_MessageData_ofName(v_head_690_);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_718_, v___x_723_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_dec_ref_known(v___x_724_, 1);
v___y_696_ = v___y_686_;
v___y_697_ = v___y_687_;
goto v___jp_695_;
}
else
{
lean_dec_ref(v_i_682_);
return v___x_724_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___boxed(lean_object* v___x_731_, lean_object* v_i_732_, lean_object* v_a_733_, lean_object* v_as_x27_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_10964__boxed_739_; lean_object* v_res_740_; 
v___x_10964__boxed_739_ = lean_unbox(v___x_731_);
v_res_740_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_10964__boxed_739_, v_i_732_, v_a_733_, v_as_x27_734_, v_b_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v_as_x27_734_);
lean_dec(v_a_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(lean_object* v___x_741_, uint8_t v___x_742_, lean_object* v_a_743_, lean_object* v___x_744_, uint8_t v___x_745_, lean_object* v_x_746_, lean_object* v_info_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
if (lean_obj_tag(v_info_747_) == 10)
{
lean_object* v_i_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_781_; 
v_i_752_ = lean_ctor_get(v_info_747_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_info_747_);
if (v_isSharedCheck_781_ == 0)
{
v___x_754_ = v_info_747_;
v_isShared_755_ = v_isSharedCheck_781_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_i_752_);
lean_dec(v_info_747_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_781_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_value_756_; lean_object* v___x_757_; 
v_value_756_ = lean_ctor_get(v_i_752_, 1);
v___x_757_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_756_, v___x_741_);
if (lean_obj_tag(v___x_757_) == 1)
{
lean_object* v_val_758_; lean_object* v___x_759_; 
lean_del_object(v___x_754_);
v_val_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_742_, v_i_752_, v_a_743_, v_val_758_, v___x_744_, v___y_749_, v___y_750_);
lean_dec(v_val_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_768_);
v___x_761_ = v___x_759_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_dec(v___x_759_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_box(v___x_745_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_a_769_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_759_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v___x_757_);
lean_dec_ref(v_i_752_);
v___x_777_ = lean_box(v___x_745_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 0);
lean_ctor_set(v___x_754_, 0, v___x_777_);
v___x_779_ = v___x_754_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_info_747_);
v___x_782_ = lean_box(v___x_745_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed(lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_a_786_, lean_object* v___x_787_, lean_object* v___x_788_, lean_object* v_x_789_, lean_object* v_info_790_, lean_object* v_x_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_11100__boxed_795_; uint8_t v___x_11103__boxed_796_; lean_object* v_res_797_; 
v___x_11100__boxed_795_ = lean_unbox(v___x_785_);
v___x_11103__boxed_796_ = lean_unbox(v___x_788_);
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(v___x_784_, v___x_11100__boxed_795_, v_a_786_, v___x_787_, v___x_11103__boxed_796_, v_x_789_, v_info_790_, v_x_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_x_791_);
lean_dec_ref(v_x_789_);
lean_dec(v_a_786_);
lean_dec(v___x_784_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(lean_object* v___x_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_798_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0___boxed(lean_object* v___x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(v___x_806_, v_x_807_, v_x_808_, v_x_809_, v_x_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v_x_810_);
lean_dec_ref(v_x_809_);
lean_dec_ref(v_x_808_);
lean_dec_ref(v_x_807_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(uint8_t v___x_819_, lean_object* v_a_820_, lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_a_820_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_b_824_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_b_824_);
v___x_830_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_831_ = lean_box(0);
v___f_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_833_ = lean_box(v___x_819_);
v___x_834_ = lean_box(v___x_828_);
lean_inc(v_a_820_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_835_, 0, v___x_830_);
lean_closure_set(v___f_835_, 1, v___x_833_);
lean_closure_set(v___f_835_, 2, v_a_820_);
lean_closure_set(v___f_835_, 3, v___x_831_);
lean_closure_set(v___f_835_, 4, v___x_834_);
v_a_836_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
v___x_837_ = lean_box(0);
lean_inc(v_a_836_);
v___x_838_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_835_, v___f_832_, v___x_837_, v_a_836_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; size_t v___x_840_; size_t v___x_841_; 
lean_dec_ref_known(v___x_838_, 1);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_823_, v___x_840_);
v_i_823_ = v___x_841_;
v_b_824_ = v___x_839_;
goto _start;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_820_);
v_a_843_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_838_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_838_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___boxed(lean_object* v___x_851_, lean_object* v_a_852_, lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v___x_11225__boxed_860_; size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v___x_11225__boxed_860_ = lean_unbox(v___x_851_);
v_sz_boxed_861_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_862_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_11225__boxed_860_, v_a_852_, v_as_853_, v_sz_boxed_861_, v_i_boxed_862_, v_b_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_as_853_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(uint8_t v___x_864_, lean_object* v_a_865_, lean_object* v_as_866_, size_t v_sz_867_, size_t v_i_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_868_, v_sz_867_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_a_865_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_b_869_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_b_869_);
v___x_875_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_876_ = lean_box(0);
v___f_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_878_ = lean_box(v___x_864_);
v___x_879_ = lean_box(v___x_873_);
lean_inc(v_a_865_);
v___f_880_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_880_, 0, v___x_875_);
lean_closure_set(v___f_880_, 1, v___x_878_);
lean_closure_set(v___f_880_, 2, v_a_865_);
lean_closure_set(v___f_880_, 3, v___x_876_);
lean_closure_set(v___f_880_, 4, v___x_879_);
v_a_881_ = lean_array_uget_borrowed(v_as_866_, v_i_868_);
v___x_882_ = lean_box(0);
lean_inc(v_a_881_);
v___x_883_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_880_, v___f_877_, v___x_882_, v_a_881_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
lean_dec_ref_known(v___x_883_, 1);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_868_, v___x_885_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_864_, v_a_865_, v_as_866_, v_sz_867_, v___x_886_, v___x_884_, v___y_870_, v___y_871_);
return v___x_887_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_865_);
v_a_888_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_883_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_883_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___boxed(lean_object* v___x_896_, lean_object* v_a_897_, lean_object* v_as_898_, lean_object* v_sz_899_, lean_object* v_i_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_11295__boxed_905_; size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v___x_11295__boxed_905_ = lean_unbox(v___x_896_);
v_sz_boxed_906_ = lean_unbox_usize(v_sz_899_);
lean_dec(v_sz_899_);
v_i_boxed_907_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_11295__boxed_905_, v_a_897_, v_as_898_, v_sz_boxed_906_, v_i_boxed_907_, v_b_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_as_898_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(uint8_t v___x_912_, lean_object* v_a_913_, lean_object* v_as_914_, size_t v_sz_915_, size_t v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec(v_a_913_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_917_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_b_917_);
v___x_923_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_924_ = lean_box(0);
v___f_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_926_ = lean_box(v___x_912_);
v___x_927_ = lean_box(v___x_921_);
lean_inc(v_a_913_);
v___f_928_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_928_, 0, v___x_923_);
lean_closure_set(v___f_928_, 1, v___x_926_);
lean_closure_set(v___f_928_, 2, v_a_913_);
lean_closure_set(v___f_928_, 3, v___x_924_);
lean_closure_set(v___f_928_, 4, v___x_927_);
v_a_929_ = lean_array_uget_borrowed(v_as_914_, v_i_916_);
v___x_930_ = lean_box(0);
lean_inc(v_a_929_);
v___x_931_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_928_, v___f_925_, v___x_930_, v_a_929_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; 
lean_dec_ref_known(v___x_931_, 1);
v___x_932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_916_, v___x_933_);
v_i_916_ = v___x_934_;
v_b_917_ = v___x_932_;
goto _start;
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_a_913_);
v_a_936_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_931_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_931_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___boxed(lean_object* v___x_944_, lean_object* v_a_945_, lean_object* v_as_946_, lean_object* v_sz_947_, lean_object* v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___x_11363__boxed_953_; size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v___x_11363__boxed_953_ = lean_unbox(v___x_944_);
v_sz_boxed_954_ = lean_unbox_usize(v_sz_947_);
lean_dec(v_sz_947_);
v_i_boxed_955_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_11363__boxed_953_, v_a_945_, v_as_946_, v_sz_boxed_954_, v_i_boxed_955_, v_b_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_as_946_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(uint8_t v___x_957_, lean_object* v_a_958_, lean_object* v_as_959_, size_t v_sz_960_, size_t v_i_961_, lean_object* v_b_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_lt(v_i_961_, v_sz_960_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v_a_958_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_b_962_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___f_973_; lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref(v_b_962_);
v___x_968_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_969_ = lean_box(0);
v___f_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_971_ = lean_box(v___x_957_);
v___x_972_ = lean_box(v___x_966_);
lean_inc(v_a_958_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_973_, 0, v___x_968_);
lean_closure_set(v___f_973_, 1, v___x_971_);
lean_closure_set(v___f_973_, 2, v_a_958_);
lean_closure_set(v___f_973_, 3, v___x_969_);
lean_closure_set(v___f_973_, 4, v___x_972_);
v_a_974_ = lean_array_uget_borrowed(v_as_959_, v_i_961_);
v___x_975_ = lean_box(0);
lean_inc(v_a_974_);
v___x_976_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_973_, v___f_970_, v___x_975_, v_a_974_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_977_; size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; 
lean_dec_ref_known(v___x_976_, 1);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_add(v_i_961_, v___x_978_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_957_, v_a_958_, v_as_959_, v_sz_960_, v___x_979_, v___x_977_, v___y_963_, v___y_964_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_958_);
v_a_981_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_976_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_976_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17___boxed(lean_object* v___x_989_, lean_object* v_a_990_, lean_object* v_as_991_, lean_object* v_sz_992_, lean_object* v_i_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
uint8_t v___x_11431__boxed_998_; size_t v_sz_boxed_999_; size_t v_i_boxed_1000_; lean_object* v_res_1001_; 
v___x_11431__boxed_998_ = lean_unbox(v___x_989_);
v_sz_boxed_999_ = lean_unbox_usize(v_sz_992_);
lean_dec(v_sz_992_);
v_i_boxed_1000_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_11431__boxed_998_, v_a_990_, v_as_991_, v_sz_boxed_999_, v_i_boxed_1000_, v_b_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_as_991_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(lean_object* v_init_1002_, uint8_t v___x_1003_, lean_object* v_a_1004_, lean_object* v_n_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
if (lean_obj_tag(v_n_1005_) == 0)
{
lean_object* v_cs_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; size_t v_sz_1013_; size_t v___x_1014_; lean_object* v___x_1015_; 
v_cs_1010_ = lean_ctor_get(v_n_1005_, 0);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_b_1006_);
v_sz_1013_ = lean_array_size(v_cs_1010_);
v___x_1014_ = ((size_t)0ULL);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1002_, v___x_1003_, v_a_1004_, v_cs_1010_, v_sz_1013_, v___x_1014_, v___x_1012_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1030_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_fst_1020_; 
v_fst_1020_ = lean_ctor_get(v_a_1016_, 0);
if (lean_obj_tag(v_fst_1020_) == 0)
{
lean_object* v_snd_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_snd_1021_ = lean_ctor_get(v_a_1016_, 1);
lean_inc(v_snd_1021_);
lean_dec(v_a_1016_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_snd_1021_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v_val_1026_; lean_object* v___x_1028_; 
lean_inc_ref(v_fst_1020_);
lean_dec(v_a_1016_);
v_val_1026_ = lean_ctor_get(v_fst_1020_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v_fst_1020_, 1);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v_val_1026_);
v___x_1028_ = v___x_1018_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_val_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1015_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1015_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_vs_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; size_t v_sz_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v_vs_1039_ = lean_ctor_get(v_n_1005_, 0);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_b_1006_);
v_sz_1042_ = lean_array_size(v_vs_1039_);
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_1003_, v_a_1004_, v_vs_1039_, v_sz_1042_, v___x_1043_, v___x_1041_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1059_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1059_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1059_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_fst_1049_; 
v_fst_1049_ = lean_ctor_get(v_a_1045_, 0);
if (lean_obj_tag(v_fst_1049_) == 0)
{
lean_object* v_snd_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v_snd_1050_ = lean_ctor_get(v_a_1045_, 1);
lean_inc(v_snd_1050_);
lean_dec(v_a_1045_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_snd_1050_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v_val_1055_; lean_object* v___x_1057_; 
lean_inc_ref(v_fst_1049_);
lean_dec(v_a_1045_);
v_val_1055_ = lean_ctor_get(v_fst_1049_, 0);
lean_inc(v_val_1055_);
lean_dec_ref_known(v_fst_1049_, 1);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_val_1055_);
v___x_1057_ = v___x_1047_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_val_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1044_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1044_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(lean_object* v_init_1068_, uint8_t v___x_1069_, lean_object* v_a_1070_, lean_object* v_as_1071_, size_t v_sz_1072_, size_t v_i_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1073_, v_sz_1072_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_a_1070_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_b_1074_);
return v___x_1079_;
}
else
{
lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1114_; 
v_snd_1080_ = lean_ctor_get(v_b_1074_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_b_1074_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v_b_1074_, 0);
lean_dec(v_unused_1115_);
v___x_1082_ = v_b_1074_;
v_isShared_1083_ = v_isSharedCheck_1114_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_dec(v_b_1074_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1114_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_array_uget_borrowed(v_as_1071_, v_i_1073_);
lean_inc(v_snd_1080_);
lean_inc(v_a_1070_);
v___x_1085_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1068_, v___x_1069_, v_a_1070_, v_a_1084_, v_snd_1080_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1105_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1105_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1105_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
if (lean_obj_tag(v_a_1086_) == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_dec(v_a_1070_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1086_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1090_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_snd_1080_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1092_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_del_object(v___x_1088_);
lean_dec(v_snd_1080_);
v_a_1097_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_a_1086_, 1);
v___x_1098_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v_a_1097_);
lean_ctor_set(v___x_1082_, 0, v___x_1098_);
v___x_1100_ = v___x_1082_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1097_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
size_t v___x_1101_; size_t v___x_1102_; 
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1073_, v___x_1101_);
v_i_1073_ = v___x_1102_;
v_b_1074_ = v___x_1100_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_del_object(v___x_1082_);
lean_dec(v_snd_1080_);
lean_dec(v_a_1070_);
v_a_1106_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1085_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1085_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16___boxed(lean_object* v_init_1116_, lean_object* v___x_1117_, lean_object* v_a_1118_, lean_object* v_as_1119_, lean_object* v_sz_1120_, lean_object* v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_11491__boxed_1126_; size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v___x_11491__boxed_1126_ = lean_unbox(v___x_1117_);
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1120_);
lean_dec(v_sz_1120_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1116_, v___x_11491__boxed_1126_, v_a_1118_, v_as_1119_, v_sz_boxed_1127_, v_i_boxed_1128_, v_b_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec_ref(v_as_1119_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12___boxed(lean_object* v_init_1130_, lean_object* v___x_1131_, lean_object* v_a_1132_, lean_object* v_n_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___x_11512__boxed_1138_; lean_object* v_res_1139_; 
v___x_11512__boxed_1138_ = lean_unbox(v___x_1131_);
v_res_1139_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1130_, v___x_11512__boxed_1138_, v_a_1132_, v_n_1133_, v_b_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_n_1133_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(uint8_t v___x_1140_, lean_object* v_a_1141_, lean_object* v_t_1142_, lean_object* v_init_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_root_1147_; lean_object* v_tail_1148_; lean_object* v___x_1149_; 
v_root_1147_ = lean_ctor_get(v_t_1142_, 0);
v_tail_1148_ = lean_ctor_get(v_t_1142_, 1);
lean_inc(v_a_1141_);
v___x_1149_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1143_, v___x_1140_, v_a_1141_, v_root_1147_, v_init_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1186_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1186_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1186_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
if (lean_obj_tag(v_a_1150_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; 
lean_dec(v_a_1141_);
v_a_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v_a_1150_, 1);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_a_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; size_t v_sz_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
lean_del_object(v___x_1152_);
v_a_1158_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v_a_1150_, 1);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1158_);
v_sz_1161_ = lean_array_size(v_tail_1148_);
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_1140_, v_a_1141_, v_tail_1148_, v_sz_1161_, v___x_1162_, v___x_1160_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1177_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1177_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1177_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_fst_1168_; 
v_fst_1168_ = lean_ctor_get(v_a_1164_, 0);
if (lean_obj_tag(v_fst_1168_) == 0)
{
lean_object* v_snd_1169_; lean_object* v___x_1171_; 
v_snd_1169_ = lean_ctor_get(v_a_1164_, 1);
lean_inc(v_snd_1169_);
lean_dec(v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_snd_1169_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_snd_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v_val_1173_; lean_object* v___x_1175_; 
lean_inc_ref(v_fst_1168_);
lean_dec(v_a_1164_);
v_val_1173_ = lean_ctor_get(v_fst_1168_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v_fst_1168_, 1);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_val_1173_);
v___x_1175_ = v___x_1166_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_val_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1163_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1163_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_a_1141_);
v_a_1187_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1149_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1149_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8___boxed(lean_object* v___x_1195_, lean_object* v_a_1196_, lean_object* v_t_1197_, lean_object* v_init_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_11698__boxed_1202_; lean_object* v_res_1203_; 
v___x_11698__boxed_1202_ = lean_unbox(v___x_1195_);
v_res_1203_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_11698__boxed_1202_, v_a_1196_, v_t_1197_, v_init_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v_t_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(lean_object* v_o_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_env_1208_; lean_object* v___x_1209_; lean_object* v_toEnvExtension_1210_; lean_object* v_asyncMode_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_merged_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
v___x_1209_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1210_ = lean_ctor_get(v___x_1209_, 0);
v_asyncMode_1211_ = lean_ctor_get(v_toEnvExtension_1210_, 2);
v___x_1212_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1213_ = lean_box(0);
v___x_1214_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1212_, v___x_1209_, v_env_1208_, v_asyncMode_1211_, v___x_1213_);
v_merged_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1214_, 1);
lean_dec(v_unused_1224_);
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_merged_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_merged_1215_);
lean_ctor_set(v___x_1217_, 0, v_o_1204_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_o_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_merged_1215_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1225_, v___y_1226_);
lean_dec(v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_scopes_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_opts_1236_; lean_object* v___x_1237_; 
v___x_1232_ = lean_st_ref_get(v___y_1230_);
v_scopes_1233_ = lean_ctor_get(v___x_1232_, 2);
lean_inc(v_scopes_1233_);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1235_ = l_List_head_x21___redArg(v___x_1234_, v_scopes_1233_);
lean_dec(v_scopes_1233_);
v_opts_1236_ = lean_ctor_get(v___x_1235_, 1);
lean_inc_ref(v_opts_1236_);
lean_dec(v___x_1235_);
v___x_1237_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_opts_1236_, v___y_1230_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0(lean_object* v_x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1246_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1243_, v___y_1244_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1244_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_1253_ = l_Lean_Linter_getLinterValue(v___x_1252_, v_a_1249_);
lean_dec(v_a_1249_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_1253_, v_a_1247_, v_a_1251_, v___x_1254_, v___y_1243_, v___y_1244_);
lean_dec(v_a_1251_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1263_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1254_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0___boxed(lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_x_1264_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object* v_o_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1280_, v___y_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object* v_o_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(uint8_t v___x_1290_, lean_object* v_i_1291_, lean_object* v_a_1292_, lean_object* v_as_1293_, lean_object* v_as_x27_1294_, lean_object* v_b_1295_, lean_object* v_a_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_1290_, v_i_1291_, v_a_1292_, v_as_x27_1294_, v_b_1295_, v___y_1297_, v___y_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object* v___x_1301_, lean_object* v_i_1302_, lean_object* v_a_1303_, lean_object* v_as_1304_, lean_object* v_as_x27_1305_, lean_object* v_b_1306_, lean_object* v_a_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v___x_11949__boxed_1311_; lean_object* v_res_1312_; 
v___x_11949__boxed_1311_ = lean_unbox(v___x_1301_);
v_res_1312_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(v___x_11949__boxed_1311_, v_i_1302_, v_a_1303_, v_as_1304_, v_as_x27_1305_, v_b_1306_, v_a_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_as_x27_1305_);
lean_dec(v_as_1304_);
lean_dec(v_a_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(lean_object* v_msgData_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_1313_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(v_msgData_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_object* v_00_u03b1_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_1324_, v___y_1325_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(v_00_u03b1_1329_, v_msg_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_object* v_00_u03b1_1335_, lean_object* v_preNode_1336_, lean_object* v_postNode_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_1336_, v_postNode_1337_, v_x_1338_, v_x_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_preNode_1345_, lean_object* v_postNode_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_00_u03b1_1344_, v_preNode_1345_, v_postNode_1346_, v_x_1347_, v_x_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1353_, lean_object* v_preNode_1354_, lean_object* v_postNode_1355_, lean_object* v___x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_1354_, v_postNode_1355_, v___x_1356_, v_x_1357_, v_x_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_preNode_1364_, lean_object* v_postNode_1365_, lean_object* v___x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(v_00_u03b1_1363_, v_preNode_1364_, v_postNode_1365_, v___x_1366_, v_x_1367_, v_x_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l_Lean_Linter_Coe_coeLinter));
v___x_1375_ = l_Lean_Elab_Command_addLinter(v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
return v_res_1377_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Coe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
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
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
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
res = initialize_Lean_Linter_Init(builtin);
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
