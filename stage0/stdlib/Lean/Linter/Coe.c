// Lean compiler output
// Module: Lean.Linter.Coe
// Imports: public import Lean.Elab.Command public import Lean.Elab.InfoTree.Util import Lean.Linter.Init import all Lean.Elab.Term.TermElabM
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t l_List_elem___at___00Lean_Elab_Term_levelMVarToParam_spec__0(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__14_value),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__17_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18_value;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_(){
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
LEAN_EXPORT void l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_26_;
v_res_26_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4____boxed(lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_2393295658____hygCtx___hyg_4_();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(lean_object* v_toPure_29_, lean_object* v_____do__lift_30_){
_start:
{
lean_object* v___x_31_; lean_object* v_name_32_; lean_object* v_map_33_; uint8_t v___x_34_; lean_object* v___x_35_; 
v___x_31_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v_name_32_ = lean_ctor_get(v___x_31_, 0);
v_map_33_ = lean_ctor_get(v_____do__lift_30_, 0);
v___x_34_ = 1;
v___x_35_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_33_, v_name_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_box(v___x_34_);
v___x_37_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_val_38_; 
v_val_38_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_val_38_);
lean_dec_ref_known(v___x_35_, 1);
if (lean_obj_tag(v_val_38_) == 1)
{
uint8_t v_v_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_v_39_ = lean_ctor_get_uint8(v_val_38_, 0);
lean_dec_ref_known(v_val_38_, 0);
v___x_40_ = lean_box(v_v_39_);
v___x_41_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_40_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_val_38_);
v___x_42_ = lean_box(v___x_34_);
v___x_43_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed(lean_object* v_toPure_44_, lean_object* v_____do__lift_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0(v_toPure_44_, v_____do__lift_45_);
lean_dec_ref(v_____do__lift_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_toApplicative_49_; lean_object* v_toBind_50_; lean_object* v_getOptions_51_; lean_object* v_toPure_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_49_ = lean_ctor_get(v_inst_47_, 0);
lean_inc_ref(v_toApplicative_49_);
v_toBind_50_ = lean_ctor_get(v_inst_47_, 1);
lean_inc(v_toBind_50_);
lean_dec_ref(v_inst_47_);
v_getOptions_51_ = lean_ctor_get(v_inst_48_, 0);
lean_inc(v_getOptions_51_);
lean_dec_ref(v_inst_48_);
v_toPure_52_ = lean_ctor_get(v_toApplicative_49_, 1);
lean_inc(v_toPure_52_);
lean_dec_ref(v_toApplicative_49_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_53_, 0, v_toPure_52_);
v___x_54_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v_getOptions_51_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(lean_object* v_m_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(v_inst_56_, v_inst_57_);
return v___x_58_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v_env_75_; lean_object* v___x_76_; lean_object* v_mainModule_77_; lean_object* v___x_78_; 
v___x_74_ = lean_st_ref_get(v___y_72_);
v_env_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_ref(v_env_75_);
lean_dec(v___x_74_);
v___x_76_ = l_Lean_Environment_header(v_env_75_);
lean_dec_ref(v_env_75_);
v_mainModule_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_mainModule_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_mainModule_77_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_72_ = stack[0].m_obj;
lean_object* v_res_79_;
v_res_79_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_72_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_80_);
lean_dec(v___y_80_);
return v_res_82_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_84_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_83_ = stack[0].m_obj;
lean_object* v___y_84_ = stack[1].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_83_, v___y_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_91_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_infoState_95_; lean_object* v_trees_96_; lean_object* v___x_97_; 
v___x_94_ = lean_st_ref_get(v___y_92_);
v_infoState_95_ = lean_ctor_get(v___x_94_, 8);
lean_inc_ref(v_infoState_95_);
lean_dec(v___x_94_);
v_trees_96_ = lean_ctor_get(v_infoState_95_, 2);
lean_inc_ref(v_trees_96_);
lean_dec_ref(v_infoState_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_trees_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_92_ = stack[0].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_92_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_102_ = stack[0].m_obj;
lean_object* v___y_103_ = stack[1].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(v___y_102_, v___y_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_110_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_instMonadEIO___redArg();
return v___x_111_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_toApplicative_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_151_; 
v___x_118_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0);
v___x_119_ = l_StateRefT_x27_instMonad___redArg(v___x_118_);
v_toApplicative_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v___x_119_, 1);
lean_dec(v_unused_152_);
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_151_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_toApplicative_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_151_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_toFunctor_124_; lean_object* v_toSeq_125_; lean_object* v_toSeqLeft_126_; lean_object* v_toSeqRight_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_149_; 
v_toFunctor_124_ = lean_ctor_get(v_toApplicative_120_, 0);
v_toSeq_125_ = lean_ctor_get(v_toApplicative_120_, 2);
v_toSeqLeft_126_ = lean_ctor_get(v_toApplicative_120_, 3);
v_toSeqRight_127_ = lean_ctor_get(v_toApplicative_120_, 4);
v_isSharedCheck_149_ = !lean_is_exclusive(v_toApplicative_120_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_toApplicative_120_, 1);
lean_dec(v_unused_150_);
v___x_129_ = v_toApplicative_120_;
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_toSeqRight_127_);
lean_inc(v_toSeqLeft_126_);
lean_inc(v_toSeq_125_);
lean_inc(v_toFunctor_124_);
lean_dec(v_toApplicative_120_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_140_; 
v___f_131_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1));
v___f_132_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2));
lean_inc_ref(v_toFunctor_124_);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_133_, 0, v_toFunctor_124_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toFunctor_124_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_133_);
lean_ctor_set(v___x_135_, 1, v___f_134_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeqRight_127_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeqLeft_126_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_138_, 0, v_toSeq_125_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___f_136_);
lean_ctor_set(v___x_129_, 3, v___f_137_);
lean_ctor_set(v___x_129_, 2, v___f_138_);
lean_ctor_set(v___x_129_, 1, v___f_131_);
lean_ctor_set(v___x_129_, 0, v___x_135_);
v___x_140_ = v___x_129_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___f_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v___f_138_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v___f_136_);
v___x_140_ = v_reuseFailAlloc_148_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___f_132_);
lean_ctor_set(v___x_122_, 0, v___x_140_);
v___x_142_ = v___x_122_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___f_132_);
v___x_142_ = v_reuseFailAlloc_147_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_8328__overap_145_; lean_object* v___x_146_; 
v___x_143_ = lean_box(0);
v___x_144_ = l_instInhabitedOfMonad___redArg(v___x_142_, v___x_143_);
v___x_8328__overap_145_ = lean_panic_fn_borrowed(v___x_144_, v_msg_114_);
lean_dec(v___x_144_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___x_146_ = lean_apply_3(v___x_8328__overap_145_, v___y_115_, v___y_116_, lean_box(0));
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_114_ = stack[0].m_obj;
lean_object* v___y_115_ = stack[1].m_obj;
lean_object* v___y_116_ = stack[2].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_114_, v___y_115_, v___y_116_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_158_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2));
v___x_163_ = lean_unsigned_to_nat(21u);
v___x_164_ = lean_unsigned_to_nat(65u);
v___x_165_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1));
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0));
v___x_167_ = l_mkPanicMessageWithDecl(v___x_166_, v___x_165_, v___x_164_, v___x_163_, v___x_162_);
return v___x_167_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(lean_object* v_preNode_168_, lean_object* v_postNode_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v_i_175_; lean_object* v_t_176_; lean_object* v___x_177_; 
v_i_175_ = lean_ctor_get(v_x_171_, 0);
lean_inc_ref(v_i_175_);
v_t_176_ = lean_ctor_get(v_x_171_, 1);
lean_inc_ref(v_t_176_);
lean_dec_ref_known(v_x_171_, 2);
v___x_177_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_175_, v_x_170_);
v_x_170_ = v___x_177_;
v_x_171_ = v_t_176_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref_known(v_x_171_, 2);
lean_dec_ref(v_postNode_169_);
lean_dec_ref(v_preNode_168_);
v___x_179_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3);
v___x_180_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v___x_179_, v___y_172_, v___y_173_);
return v___x_180_;
}
else
{
lean_object* v_i_181_; lean_object* v_children_182_; lean_object* v_val_183_; lean_object* v___x_184_; 
v_i_181_ = lean_ctor_get(v_x_171_, 0);
lean_inc_ref_n(v_i_181_, 2);
v_children_182_ = lean_ctor_get(v_x_171_, 1);
lean_inc_ref_n(v_children_182_, 2);
lean_dec_ref_known(v_x_171_, 2);
v_val_183_ = lean_ctor_get(v_x_170_, 0);
lean_inc_n(v_val_183_, 2);
lean_inc_ref(v_preNode_168_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
v___x_184_ = lean_apply_6(v_preNode_168_, v_val_183_, v_i_181_, v_children_182_, v___y_172_, v___y_173_, lean_box(0));
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; uint8_t v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v___x_186_ = lean_unbox(v_a_185_);
lean_dec(v_a_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_preNode_168_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_170_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_x_170_, 0);
lean_dec(v_unused_212_);
v___x_188_ = v_x_170_;
v_isShared_189_ = v_isSharedCheck_211_;
goto v_resetjp_187_;
}
else
{
lean_dec(v_x_170_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_211_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(0);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
v___x_191_ = lean_apply_7(v_postNode_169_, v_val_183_, v_i_181_, v_children_182_, v___x_190_, v___y_172_, v___y_173_, lean_box(0));
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_202_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_202_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_a_192_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_del_object(v___x_188_);
v_a_203_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_191_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_191_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_Elab_Info_updateContext_x3f(v_x_170_, v_i_181_);
v___x_214_ = l_Lean_PersistentArray_toList___redArg(v_children_182_);
v___x_215_ = lean_box(0);
lean_inc_ref(v_postNode_169_);
v___x_216_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_168_, v_postNode_169_, v___x_213_, v___x_214_, v___x_215_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
v___x_218_ = lean_apply_7(v_postNode_169_, v_val_183_, v_i_181_, v_children_182_, v_a_217_, v___y_172_, v___y_173_, lean_box(0));
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_a_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_218_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_val_183_);
lean_dec_ref(v_children_182_);
lean_dec_ref(v_i_181_);
lean_dec_ref(v_postNode_169_);
v_a_236_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_216_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_216_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_val_183_);
lean_dec_ref(v_children_182_);
lean_dec_ref_known(v_x_170_, 1);
lean_dec_ref(v_i_181_);
lean_dec_ref(v_postNode_169_);
lean_dec_ref(v_preNode_168_);
v_a_244_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_184_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_184_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
default: 
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_x_170_);
lean_dec_ref(v_postNode_169_);
lean_dec_ref(v_preNode_168_);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; 
v_unused_260_ = lean_ctor_get(v_x_171_, 0);
lean_dec(v_unused_260_);
v___x_253_ = v_x_171_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_x_171_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 0);
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_168_ = stack[0].m_obj;
lean_object* v_postNode_169_ = stack[1].m_obj;
lean_object* v_x_170_ = stack[2].m_obj;
lean_object* v_x_171_ = stack[3].m_obj;
lean_object* v___y_172_ = stack[4].m_obj;
lean_object* v___y_173_ = stack[5].m_obj;
lean_object* v_res_261_;
v_res_261_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_168_, v_postNode_169_, v_x_170_, v_x_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_261_;
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(lean_object* v_preNode_262_, lean_object* v_postNode_263_, lean_object* v___x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v___x_264_);
lean_dec_ref(v_postNode_263_);
lean_dec_ref(v_preNode_262_);
v___x_270_ = l_List_reverse___redArg(v_x_266_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_291_; 
v_head_272_ = lean_ctor_get(v_x_265_, 0);
v_tail_273_ = lean_ctor_get(v_x_265_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_291_ == 0)
{
v___x_275_ = v_x_265_;
v_isShared_276_ = v_isSharedCheck_291_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_tail_273_);
lean_inc(v_head_272_);
lean_dec(v_x_265_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_291_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; 
lean_inc(v___x_264_);
lean_inc_ref(v_postNode_263_);
lean_inc_ref(v_preNode_262_);
v___x_277_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_262_, v_postNode_263_, v___x_264_, v_head_272_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_x_266_);
lean_ctor_set(v___x_275_, 0, v_a_278_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_278_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_x_266_);
v___x_280_ = v_reuseFailAlloc_282_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v_x_265_ = v_tail_273_;
v_x_266_ = v___x_280_;
goto _start;
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_del_object(v___x_275_);
lean_dec(v_tail_273_);
lean_dec(v_x_266_);
lean_dec(v___x_264_);
lean_dec_ref(v_postNode_263_);
lean_dec_ref(v_preNode_262_);
v_a_283_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_277_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_262_ = stack[0].m_obj;
lean_object* v_postNode_263_ = stack[1].m_obj;
lean_object* v___x_264_ = stack[2].m_obj;
lean_object* v_x_265_ = stack[3].m_obj;
lean_object* v_x_266_ = stack[4].m_obj;
lean_object* v___y_267_ = stack[5].m_obj;
lean_object* v___y_268_ = stack[6].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_262_, v_postNode_263_, v___x_264_, v_x_265_, v_x_266_, v___y_267_, v___y_268_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_preNode_293_, lean_object* v_postNode_294_, lean_object* v___x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_293_, v_postNode_294_, v___x_295_, v_x_296_, v_x_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___boxed(lean_object* v_preNode_302_, lean_object* v_postNode_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_302_, v_postNode_303_, v_x_304_, v_x_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_309_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(lean_object* v_postNode_310_, lean_object* v_ci_311_, lean_object* v_i_312_, lean_object* v_cs_313_, lean_object* v_x_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
v___x_318_ = lean_apply_6(v_postNode_310_, v_ci_311_, v_i_312_, v_cs_313_, v___y_315_, v___y_316_, lean_box(0));
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_postNode_310_ = stack[0].m_obj;
lean_object* v_ci_311_ = stack[1].m_obj;
lean_object* v_i_312_ = stack[2].m_obj;
lean_object* v_cs_313_ = stack[3].m_obj;
lean_object* v_x_314_ = stack[4].m_obj;
lean_object* v___y_315_ = stack[5].m_obj;
lean_object* v___y_316_ = stack[6].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(v_postNode_310_, v_ci_311_, v_i_312_, v_cs_313_, v_x_314_, v___y_315_, v___y_316_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed(lean_object* v_postNode_320_, lean_object* v_ci_321_, lean_object* v_i_322_, lean_object* v_cs_323_, lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(v_postNode_320_, v_ci_321_, v_i_322_, v_cs_323_, v_x_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v_x_324_);
return v_res_328_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(lean_object* v_preNode_329_, lean_object* v_postNode_330_, lean_object* v_ctx_x3f_331_, lean_object* v_t_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(v___f_336_, 0, v_postNode_330_);
v___x_337_ = lean_box(0);
v___x_338_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_329_, v___f_336_, v_ctx_x3f_331_, v_t_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v___x_338_, 0);
lean_dec(v_unused_346_);
v___x_340_ = v___x_338_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_dec(v___x_338_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_337_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_337_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_338_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_338_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_329_ = stack[0].m_obj;
lean_object* v_postNode_330_ = stack[1].m_obj;
lean_object* v_ctx_x3f_331_ = stack[2].m_obj;
lean_object* v_t_332_ = stack[3].m_obj;
lean_object* v___y_333_ = stack[4].m_obj;
lean_object* v___y_334_ = stack[5].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v_preNode_329_, v_postNode_330_, v_ctx_x3f_331_, v_t_332_, v___y_333_, v___y_334_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object* v_preNode_356_, lean_object* v_postNode_357_, lean_object* v_ctx_x3f_358_, lean_object* v_t_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v_preNode_356_, v_postNode_357_, v_ctx_x3f_358_, v_t_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_364_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
lean_ctor_set(v___x_370_, 3, v___x_369_);
lean_ctor_set(v___x_370_, 4, v___x_368_);
lean_ctor_set(v___x_370_, 5, v___x_368_);
lean_ctor_set(v___x_370_, 6, v___x_368_);
lean_ctor_set(v___x_370_, 7, v___x_368_);
lean_ctor_set(v___x_370_, 8, v___x_368_);
lean_ctor_set(v___x_370_, 9, v___x_368_);
lean_ctor_set(v___x_370_, 10, v___x_368_);
lean_ctor_set(v___x_370_, 11, v___x_367_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_unsigned_to_nat(32u);
v___x_372_ = lean_mk_empty_array_with_capacity(v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_374_ = ((size_t)5ULL);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_unsigned_to_nat(32u);
v___x_377_ = lean_mk_empty_array_with_capacity(v___x_376_);
v___x_378_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3);
v___x_379_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_375_);
lean_ctor_set(v___x_379_, 3, v___x_375_);
lean_ctor_set_usize(v___x_379_, 4, v___x_374_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_box(1);
v___x_381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4);
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_380_);
return v___x_383_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(lean_object* v_msgData_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_env_388_; uint8_t v___x_389_; lean_object* v_env_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_scopes_393_; lean_object* v___x_394_; lean_object* v_opts_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_387_ = lean_st_ref_get(v___y_385_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = 0;
v_env_390_ = l_Lean_Environment_setRecordingDeps(v_env_388_, v___x_389_);
v___x_391_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_392_ = lean_st_ref_get(v___y_385_);
v_scopes_393_ = lean_ctor_get(v___x_392_, 2);
lean_inc(v_scopes_393_);
lean_dec(v___x_392_);
v___x_394_ = l_List_head_x21___redArg(v___x_391_, v_scopes_393_);
lean_dec(v_scopes_393_);
v_opts_395_ = lean_ctor_get(v___x_394_, 1);
lean_inc_ref(v_opts_395_);
lean_dec(v___x_394_);
v___x_396_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2);
v___x_397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5);
v___x_398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_398_, 0, v_env_390_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_397_);
lean_ctor_set(v___x_398_, 3, v_opts_395_);
v___x_399_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_msgData_384_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_384_ = stack[0].m_obj;
lean_object* v___y_385_ = stack[1].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_384_, v___y_385_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_402_, v___y_403_);
lean_dec(v___y_403_);
return v_res_405_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(uint8_t v_suppressElabErrors_407_, uint8_t v___y_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 1)
{
lean_object* v_pre_410_; 
v_pre_410_ = lean_ctor_get(v_x_409_, 0);
if (lean_obj_tag(v_pre_410_) == 0)
{
lean_object* v_str_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_str_411_ = lean_ctor_get(v_x_409_, 1);
v___x_412_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0));
v___x_413_ = lean_string_dec_eq(v_str_411_, v___x_412_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
return v_suppressElabErrors_407_;
}
}
else
{
return v___y_408_;
}
}
else
{
return v___y_408_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_407_ = stack[0].m_num;
uint8_t v___y_408_ = stack[1].m_num;
lean_object* v_x_409_ = stack[2].m_obj;
uint8_t v_res_414_;
v_res_414_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(v_suppressElabErrors_407_, v___y_408_, v_x_409_);
stack->m_num = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_415_, lean_object* v___y_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_suppressElabErrors_boxed_418_; uint8_t v___y_10811__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_suppressElabErrors_boxed_418_ = lean_unbox(v_suppressElabErrors_415_);
v___y_10811__boxed_419_ = lean_unbox(v___y_416_);
v_res_420_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(v_suppressElabErrors_boxed_418_, v___y_10811__boxed_419_, v_x_417_);
lean_dec(v_x_417_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(lean_object* v_ref_423_, lean_object* v_msgData_424_, uint8_t v_severity_425_, uint8_t v_isSilent_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; uint8_t v___y_496_; uint8_t v___y_497_; lean_object* v___y_498_; uint8_t v___y_499_; lean_object* v___y_500_; uint8_t v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; uint8_t v___y_532_; uint8_t v___y_533_; uint8_t v___y_534_; uint8_t v___x_549_; uint8_t v___y_551_; uint8_t v___y_552_; uint8_t v___y_553_; uint8_t v___y_555_; uint8_t v___x_567_; 
v___x_549_ = 2;
v___x_567_ = l_Lean_instBEqMessageSeverity_beq(v_severity_425_, v___x_549_);
if (v___x_567_ == 0)
{
v___y_555_ = v___x_567_;
goto v___jp_554_;
}
else
{
uint8_t v___x_568_; 
lean_inc_ref(v_msgData_424_);
v___x_568_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_424_);
v___y_555_ = v___x_568_;
goto v___jp_554_;
}
v___jp_430_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Elab_Command_getScope___redArg(v___y_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_currNamespace_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v_currNamespace_441_ = lean_ctor_get(v_a_440_, 2);
lean_inc(v_currNamespace_441_);
lean_dec(v_a_440_);
v___x_442_ = l_Lean_Elab_Command_getScope___redArg(v___y_438_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_478_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_478_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_478_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_478_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_openDecls_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_env_452_; lean_object* v_messages_453_; lean_object* v_scopes_454_; lean_object* v_usedQuotCtxts_455_; lean_object* v_nextMacroScope_456_; lean_object* v_maxRecDepth_457_; lean_object* v_ngen_458_; lean_object* v_auxDeclNGen_459_; lean_object* v_infoState_460_; lean_object* v_traceState_461_; lean_object* v_snapshotTasks_462_; lean_object* v_prevLinterStates_463_; lean_object* v_codeQualityEntryTasks_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_477_; 
v_openDecls_447_ = lean_ctor_get(v_a_443_, 3);
lean_inc(v_openDecls_447_);
lean_dec(v_a_443_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_currNamespace_441_);
lean_ctor_set(v___x_448_, 1, v_openDecls_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc_ref(v___y_434_);
v___x_450_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_450_, 0, v___y_434_);
lean_ctor_set(v___x_450_, 1, v___y_432_);
lean_ctor_set(v___x_450_, 2, v___y_433_);
lean_ctor_set(v___x_450_, 3, v___y_435_);
lean_ctor_set(v___x_450_, 4, v___x_449_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5, v___y_437_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 1, v___y_431_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 2, v_isSilent_426_);
v___x_451_ = lean_st_ref_take(v___y_438_);
v_env_452_ = lean_ctor_get(v___x_451_, 0);
v_messages_453_ = lean_ctor_get(v___x_451_, 1);
v_scopes_454_ = lean_ctor_get(v___x_451_, 2);
v_usedQuotCtxts_455_ = lean_ctor_get(v___x_451_, 3);
v_nextMacroScope_456_ = lean_ctor_get(v___x_451_, 4);
v_maxRecDepth_457_ = lean_ctor_get(v___x_451_, 5);
v_ngen_458_ = lean_ctor_get(v___x_451_, 6);
v_auxDeclNGen_459_ = lean_ctor_get(v___x_451_, 7);
v_infoState_460_ = lean_ctor_get(v___x_451_, 8);
v_traceState_461_ = lean_ctor_get(v___x_451_, 9);
v_snapshotTasks_462_ = lean_ctor_get(v___x_451_, 10);
v_prevLinterStates_463_ = lean_ctor_get(v___x_451_, 11);
v_codeQualityEntryTasks_464_ = lean_ctor_get(v___x_451_, 12);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_477_ == 0)
{
v___x_466_ = v___x_451_;
v_isShared_467_ = v_isSharedCheck_477_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_codeQualityEntryTasks_464_);
lean_inc(v_prevLinterStates_463_);
lean_inc(v_snapshotTasks_462_);
lean_inc(v_traceState_461_);
lean_inc(v_infoState_460_);
lean_inc(v_auxDeclNGen_459_);
lean_inc(v_ngen_458_);
lean_inc(v_maxRecDepth_457_);
lean_inc(v_nextMacroScope_456_);
lean_inc(v_usedQuotCtxts_455_);
lean_inc(v_scopes_454_);
lean_inc(v_messages_453_);
lean_inc(v_env_452_);
lean_dec(v___x_451_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_477_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_MessageLog_add(v___x_450_, v_messages_453_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_env_452_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_scopes_454_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_usedQuotCtxts_455_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_nextMacroScope_456_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v_maxRecDepth_457_);
lean_ctor_set(v_reuseFailAlloc_476_, 6, v_ngen_458_);
lean_ctor_set(v_reuseFailAlloc_476_, 7, v_auxDeclNGen_459_);
lean_ctor_set(v_reuseFailAlloc_476_, 8, v_infoState_460_);
lean_ctor_set(v_reuseFailAlloc_476_, 9, v_traceState_461_);
lean_ctor_set(v_reuseFailAlloc_476_, 10, v_snapshotTasks_462_);
lean_ctor_set(v_reuseFailAlloc_476_, 11, v_prevLinterStates_463_);
lean_ctor_set(v_reuseFailAlloc_476_, 12, v_codeQualityEntryTasks_464_);
v___x_471_ = v_reuseFailAlloc_476_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_st_ref_put(v___y_438_, v___x_471_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_468_);
v___x_474_ = v___x_445_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_468_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_currNamespace_441_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
v_a_479_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_442_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_442_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v___y_436_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
v_a_487_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_439_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_439_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
v___jp_495_:
{
lean_object* v_fileName_501_; lean_object* v_fileMap_502_; uint8_t v_suppressElabErrors_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_522_; 
v_fileName_501_ = lean_ctor_get(v___y_427_, 0);
v_fileMap_502_ = lean_ctor_get(v___y_427_, 1);
v_suppressElabErrors_503_ = lean_ctor_get_uint8(v___y_427_, sizeof(void*)*10);
v___x_504_ = lean_box(v_suppressElabErrors_503_);
v___x_505_ = lean_box(v___y_496_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_506_, 0, v___x_504_);
lean_closure_set(v___f_506_, 1, v___x_505_);
v___x_507_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_424_);
v___x_508_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v___x_507_, v___y_428_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_522_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_inc_ref_n(v_fileMap_502_, 2);
v___x_513_ = l_Lean_FileMap_toPosition(v_fileMap_502_, v___y_498_);
lean_dec(v___y_498_);
v___x_514_ = l_Lean_FileMap_toPosition(v_fileMap_502_, v___y_500_);
lean_dec(v___y_500_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0));
if (v_suppressElabErrors_503_ == 0)
{
lean_del_object(v___x_511_);
lean_dec_ref(v___f_506_);
v___y_431_ = v___y_497_;
v___y_432_ = v___x_513_;
v___y_433_ = v___x_515_;
v___y_434_ = v_fileName_501_;
v___y_435_ = v___x_516_;
v___y_436_ = v_a_509_;
v___y_437_ = v___y_499_;
v___y_438_ = v___y_428_;
goto v___jp_430_;
}
else
{
uint8_t v___x_517_; 
lean_inc(v_a_509_);
v___x_517_ = l_Lean_MessageData_hasTag(v___f_506_, v_a_509_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec_ref_known(v___x_515_, 1);
lean_dec_ref(v___x_513_);
lean_dec(v_a_509_);
v___x_518_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_518_);
v___x_520_ = v___x_511_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_del_object(v___x_511_);
v___y_431_ = v___y_497_;
v___y_432_ = v___x_513_;
v___y_433_ = v___x_515_;
v___y_434_ = v_fileName_501_;
v___y_435_ = v___x_516_;
v___y_436_ = v_a_509_;
v___y_437_ = v___y_499_;
v___y_438_ = v___y_428_;
goto v___jp_430_;
}
}
}
}
v___jp_523_:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Syntax_getTailPos_x3f(v___y_526_, v___y_527_);
lean_dec(v___y_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_inc(v___y_528_);
v___y_496_ = v___y_524_;
v___y_497_ = v___y_525_;
v___y_498_ = v___y_528_;
v___y_499_ = v___y_527_;
v___y_500_ = v___y_528_;
goto v___jp_495_;
}
else
{
lean_object* v_val_530_; 
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_529_, 1);
v___y_496_ = v___y_524_;
v___y_497_ = v___y_525_;
v___y_498_ = v___y_528_;
v___y_499_ = v___y_527_;
v___y_500_ = v_val_530_;
goto v___jp_495_;
}
}
v___jp_531_:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Elab_Command_getRef___redArg(v___y_427_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_ref_537_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v_ref_537_ = l_Lean_replaceRef(v_ref_423_, v_a_536_);
lean_dec(v_a_536_);
v___x_538_ = l_Lean_Syntax_getPos_x3f(v_ref_537_, v___y_533_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___y_524_ = v___y_532_;
v___y_525_ = v___y_534_;
v___y_526_ = v_ref_537_;
v___y_527_ = v___y_533_;
v___y_528_ = v___x_539_;
goto v___jp_523_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_538_, 1);
v___y_524_ = v___y_532_;
v___y_525_ = v___y_534_;
v___y_526_ = v_ref_537_;
v___y_527_ = v___y_533_;
v___y_528_ = v_val_540_;
goto v___jp_523_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_msgData_424_);
v_a_541_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_535_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_535_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
v___jp_550_:
{
if (v___y_553_ == 0)
{
v___y_532_ = v___y_551_;
v___y_533_ = v___y_552_;
v___y_534_ = v_severity_425_;
goto v___jp_531_;
}
else
{
v___y_532_ = v___y_551_;
v___y_533_ = v___y_552_;
v___y_534_ = v___x_549_;
goto v___jp_531_;
}
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_scopes_558_; lean_object* v___x_559_; lean_object* v_opts_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_556_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_557_ = lean_st_ref_get(v___y_428_);
v_scopes_558_ = lean_ctor_get(v___x_557_, 2);
lean_inc(v_scopes_558_);
lean_dec(v___x_557_);
v___x_559_ = l_List_head_x21___redArg(v___x_556_, v_scopes_558_);
lean_dec(v_scopes_558_);
v_opts_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc_ref(v_opts_560_);
lean_dec(v___x_559_);
v___x_561_ = 1;
v___x_562_ = l_Lean_instBEqMessageSeverity_beq(v_severity_425_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_opts_560_);
v___y_551_ = v___y_555_;
v___y_552_ = v___y_555_;
v___y_553_ = v___x_562_;
goto v___jp_550_;
}
else
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = l_Lean_warningAsError;
v___x_564_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(v_opts_560_, v___x_563_);
lean_dec_ref(v_opts_560_);
v___y_551_ = v___y_555_;
v___y_552_ = v___y_555_;
v___y_553_ = v___x_564_;
goto v___jp_550_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_msgData_424_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_423_ = stack[0].m_obj;
lean_object* v_msgData_424_ = stack[1].m_obj;
uint8_t v_severity_425_ = stack[2].m_num;
uint8_t v_isSilent_426_ = stack[3].m_num;
lean_object* v___y_427_ = stack[4].m_obj;
lean_object* v___y_428_ = stack[5].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_423_, v_msgData_424_, v_severity_425_, v_isSilent_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___boxed(lean_object* v_ref_570_, lean_object* v_msgData_571_, lean_object* v_severity_572_, lean_object* v_isSilent_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_severity_boxed_577_; uint8_t v_isSilent_boxed_578_; lean_object* v_res_579_; 
v_severity_boxed_577_ = lean_unbox(v_severity_572_);
v_isSilent_boxed_578_ = lean_unbox(v_isSilent_573_);
v_res_579_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_570_, v_msgData_571_, v_severity_boxed_577_, v_isSilent_boxed_578_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v_ref_570_);
return v_res_579_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(lean_object* v_ref_580_, lean_object* v_msgData_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = 1;
v___x_586_ = 0;
v___x_587_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_580_, v_msgData_581_, v___x_585_, v___x_586_, v___y_582_, v___y_583_);
return v___x_587_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_580_ = stack[0].m_obj;
lean_object* v_msgData_581_ = stack[1].m_obj;
lean_object* v___y_582_ = stack[2].m_obj;
lean_object* v___y_583_ = stack[3].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_ref_580_, v_msgData_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object* v_ref_589_, lean_object* v_msgData_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_ref_589_, v_msgData_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v_ref_589_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0));
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(lean_object* v_linterOption_601_, lean_object* v_stx_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_name_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_625_; 
v_name_607_ = lean_ctor_get(v_linterOption_601_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_linterOption_601_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_linterOption_601_, 1);
lean_dec(v_unused_626_);
v___x_609_ = v_linterOption_601_;
v_isShared_610_ = v_isSharedCheck_625_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_name_607_);
lean_dec(v_linterOption_601_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_625_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1);
lean_inc(v_name_607_);
v___x_612_ = l_Lean_MessageData_ofName(v_name_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 7);
lean_ctor_set(v___x_609_, 1, v___x_612_);
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_624_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_disable_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_615_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v_disable_617_ = l_Lean_MessageData_note(v___x_616_);
v___x_618_ = l_Lean_Linter_linterMessageTag;
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v_msg_603_);
lean_ctor_set(v___x_619_, 1, v_disable_617_);
v___x_620_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_621_, 0, v_name_607_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc(v_stx_602_);
v___x_622_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_622_, 0, v_stx_602_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_602_, v___x_622_, v___y_604_, v___y_605_);
lean_dec(v_stx_602_);
return v___x_623_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_601_ = stack[0].m_obj;
lean_object* v_stx_602_ = stack[1].m_obj;
lean_object* v_msg_603_ = stack[2].m_obj;
lean_object* v___y_604_ = stack[3].m_obj;
lean_object* v___y_605_ = stack[4].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v_linterOption_601_, v_stx_602_, v_msg_603_, v___y_604_, v___y_605_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(lean_object* v_linterOption_628_, lean_object* v_stx_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v_linterOption_628_, v_stx_629_, v_msg_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_634_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object* v_a_635_, lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v___x_641_ = lean_name_eq(v_a_635_, v___x_640_);
if (v___x_641_ == 0)
{
size_t v___x_642_; size_t v___x_643_; 
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_i_637_, v___x_642_);
v_i_637_ = v___x_643_;
goto _start;
}
else
{
return v___x_641_;
}
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_635_ = stack[0].m_obj;
lean_object* v_as_636_ = stack[1].m_obj;
size_t v_i_637_ = stack[2].m_num;
size_t v_stop_638_ = stack[3].m_num;
uint8_t v_res_646_;
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_635_, v_as_636_, v_i_637_, v_stop_638_);
stack->m_num = v_res_646_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object* v_a_647_, lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_647_, v_as_648_, v_i_boxed_651_, v_stop_boxed_652_);
lean_dec_ref(v_as_648_);
lean_dec(v_a_647_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
uint8_t l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object* v_as_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_as_655_);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
return v___x_659_;
}
else
{
if (v___x_659_ == 0)
{
return v___x_659_;
}
else
{
size_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_658_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_656_, v_as_655_, v___x_660_, v___x_661_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_655_ = stack[0].m_obj;
lean_object* v_a_656_ = stack[1].m_obj;
uint8_t v_res_663_;
v_res_663_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v_as_655_, v_a_656_);
stack->m_num = v_res_663_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object* v_as_664_, lean_object* v_a_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v_as_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_as_664_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(uint8_t v___x_702_, lean_object* v_i_703_, lean_object* v_a_704_, lean_object* v_as_x27_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
if (lean_obj_tag(v_as_x27_705_) == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v_i_703_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_b_706_);
return v___x_710_;
}
else
{
lean_object* v_head_711_; lean_object* v_tail_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_736_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_head_711_ = lean_ctor_get(v_as_x27_705_, 0);
v_tail_712_ = lean_ctor_get(v_as_x27_705_, 1);
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_715_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12));
v___x_747_ = lean_name_eq(v_a_704_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = l_Lean_Name_getRoot(v_a_704_);
v___x_749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18));
v___x_750_ = l_List_elem___at___00Lean_Elab_Term_levelMVarToParam_spec__0(v___x_748_, v___x_749_);
lean_dec(v___x_748_);
v___y_736_ = v___x_750_;
goto v___jp_735_;
}
else
{
v___y_736_ = v___x_747_;
goto v___jp_735_;
}
v___jp_716_:
{
if (v___x_702_ == 0)
{
v_as_x27_705_ = v_tail_712_;
v_b_706_ = v___x_713_;
goto _start;
}
else
{
lean_object* v___x_720_; lean_object* v_env_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_st_ref_get(v___y_718_);
v_env_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_env_721_);
lean_dec(v___x_720_);
v___x_722_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_head_711_);
v___x_723_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_714_, v___x_722_, v_env_721_, v_head_711_);
if (lean_obj_tag(v___x_723_) == 1)
{
lean_object* v_stx_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref_known(v___x_723_, 1);
v_stx_724_ = lean_ctor_get(v_i_703_, 0);
v___x_725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1));
v___x_726_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3);
lean_inc(v_head_711_);
v___x_727_ = l_Lean_MessageData_ofConstName(v_head_711_, v___x_702_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_725_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc(v_stx_724_);
v___x_732_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v___x_715_, v_stx_724_, v___x_731_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
v_as_x27_705_ = v_tail_712_;
v_b_706_ = v___x_713_;
goto _start;
}
else
{
lean_dec_ref(v_i_703_);
return v___x_732_;
}
}
else
{
lean_dec(v___x_723_);
v_as_x27_705_ = v_tail_712_;
v_b_706_ = v___x_713_;
goto _start;
}
}
}
v___jp_735_:
{
if (v___y_736_ == 0)
{
v___y_717_ = v___y_707_;
v___y_718_ = v___y_708_;
goto v___jp_716_;
}
else
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_Linter_Coe_coercionsBannedInCore));
v___x_738_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v___x_737_, v_head_711_);
if (v___x_738_ == 0)
{
v___y_717_ = v___y_707_;
v___y_718_ = v___y_708_;
goto v___jp_716_;
}
else
{
lean_object* v_stx_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_stx_739_ = lean_ctor_get(v_i_703_, 0);
v___x_740_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7);
lean_inc(v_head_711_);
v___x_741_ = l_Lean_MessageData_ofName(v_head_711_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_739_, v___x_744_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec_ref_known(v___x_745_, 1);
v___y_717_ = v___y_707_;
v___y_718_ = v___y_708_;
goto v___jp_716_;
}
else
{
lean_dec_ref(v_i_703_);
return v___x_745_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_702_ = stack[0].m_num;
lean_object* v_i_703_ = stack[1].m_obj;
lean_object* v_a_704_ = stack[2].m_obj;
lean_object* v_as_x27_705_ = stack[3].m_obj;
lean_object* v_b_706_ = stack[4].m_obj;
lean_object* v___y_707_ = stack[5].m_obj;
lean_object* v___y_708_ = stack[6].m_obj;
lean_object* v_res_751_;
v_res_751_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_702_, v_i_703_, v_a_704_, v_as_x27_705_, v_b_706_, v___y_707_, v___y_708_);
stack->m_obj
 = v_res_751_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___boxed(lean_object* v___x_752_, lean_object* v_i_753_, lean_object* v_a_754_, lean_object* v_as_x27_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v___x_11439__boxed_760_; lean_object* v_res_761_; 
v___x_11439__boxed_760_ = lean_unbox(v___x_752_);
v_res_761_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_11439__boxed_760_, v_i_753_, v_a_754_, v_as_x27_755_, v_b_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_as_x27_755_);
lean_dec(v_a_754_);
return v_res_761_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(lean_object* v___x_762_, uint8_t v___x_763_, lean_object* v_a_764_, lean_object* v___x_765_, uint8_t v___x_766_, lean_object* v_x_767_, lean_object* v_info_768_, lean_object* v_x_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
if (lean_obj_tag(v_info_768_) == 10)
{
lean_object* v_i_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_802_; 
v_i_773_ = lean_ctor_get(v_info_768_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_info_768_);
if (v_isSharedCheck_802_ == 0)
{
v___x_775_ = v_info_768_;
v_isShared_776_ = v_isSharedCheck_802_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_i_773_);
lean_dec(v_info_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_802_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_value_777_; lean_object* v___x_778_; 
v_value_777_ = lean_ctor_get(v_i_773_, 1);
v___x_778_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_777_, v___x_762_);
if (lean_obj_tag(v___x_778_) == 1)
{
lean_object* v_val_779_; lean_object* v___x_780_; 
lean_del_object(v___x_775_);
v_val_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_763_, v_i_773_, v_a_764_, v_val_779_, v___x_765_, v___y_770_, v___y_771_);
lean_dec(v_val_779_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_780_, 0);
lean_dec(v_unused_789_);
v___x_782_ = v___x_780_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_dec(v___x_780_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_box(v___x_766_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_780_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v___x_778_);
lean_dec_ref(v_i_773_);
v___x_798_ = lean_box(v___x_766_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 0);
lean_ctor_set(v___x_775_, 0, v___x_798_);
v___x_800_ = v___x_775_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v_info_768_);
v___x_803_ = lean_box(v___x_766_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_762_ = stack[0].m_obj;
uint8_t v___x_763_ = stack[1].m_num;
lean_object* v_a_764_ = stack[2].m_obj;
lean_object* v___x_765_ = stack[3].m_obj;
uint8_t v___x_766_ = stack[4].m_num;
lean_object* v_x_767_ = stack[5].m_obj;
lean_object* v_info_768_ = stack[6].m_obj;
lean_object* v_x_769_ = stack[7].m_obj;
lean_object* v___y_770_ = stack[8].m_obj;
lean_object* v___y_771_ = stack[9].m_obj;
lean_object* v_res_805_;
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(v___x_762_, v___x_763_, v_a_764_, v___x_765_, v___x_766_, v_x_767_, v_info_768_, v_x_769_, v___y_770_, v___y_771_);
stack->m_obj
 = v_res_805_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed(lean_object* v___x_806_, lean_object* v___x_807_, lean_object* v_a_808_, lean_object* v___x_809_, lean_object* v___x_810_, lean_object* v_x_811_, lean_object* v_info_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_11656__boxed_817_; uint8_t v___x_11659__boxed_818_; lean_object* v_res_819_; 
v___x_11656__boxed_817_ = lean_unbox(v___x_807_);
v___x_11659__boxed_818_ = lean_unbox(v___x_810_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(v___x_806_, v___x_11656__boxed_817_, v_a_808_, v___x_809_, v___x_11659__boxed_818_, v_x_811_, v_info_812_, v_x_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec_ref(v_x_813_);
lean_dec_ref(v_x_811_);
lean_dec(v_a_808_);
lean_dec(v___x_806_);
return v_res_819_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(lean_object* v___x_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_820_);
return v___x_827_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_820_ = stack[0].m_obj;
lean_object* v_x_821_ = stack[1].m_obj;
lean_object* v_x_822_ = stack[2].m_obj;
lean_object* v_x_823_ = stack[3].m_obj;
lean_object* v_x_824_ = stack[4].m_obj;
lean_object* v___y_825_ = stack[5].m_obj;
lean_object* v_res_828_;
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(v___x_820_, v_x_821_, v_x_822_, v_x_823_, v_x_824_, v___y_825_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0___boxed(lean_object* v___x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(v___x_829_, v_x_830_, v_x_831_, v_x_832_, v_x_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_830_);
return v_res_836_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(uint8_t v___x_842_, lean_object* v_a_843_, lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_dec(v_a_843_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_b_847_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v_a_860_; lean_object* v___x_861_; 
lean_dec_ref(v_b_847_);
v___x_853_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_854_ = lean_box(0);
v___f_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_856_ = lean_box(v___x_842_);
v___x_857_ = lean_box(v___x_851_);
lean_inc(v_a_843_);
v___f_858_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_858_, 0, v___x_853_);
lean_closure_set(v___f_858_, 1, v___x_856_);
lean_closure_set(v___f_858_, 2, v_a_843_);
lean_closure_set(v___f_858_, 3, v___x_854_);
lean_closure_set(v___f_858_, 4, v___x_857_);
v___x_859_ = lean_box(0);
v_a_860_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
lean_inc(v_a_860_);
v___x_861_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_858_, v___f_855_, v___x_859_, v_a_860_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; size_t v___x_863_; size_t v___x_864_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_863_ = ((size_t)1ULL);
v___x_864_ = lean_usize_add(v_i_846_, v___x_863_);
v_i_846_ = v___x_864_;
v_b_847_ = v___x_862_;
goto _start;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_843_);
v_a_866_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_861_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_861_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_842_ = stack[0].m_num;
lean_object* v_a_843_ = stack[1].m_obj;
lean_object* v_as_844_ = stack[2].m_obj;
size_t v_sz_845_ = stack[3].m_num;
size_t v_i_846_ = stack[4].m_num;
lean_object* v_b_847_ = stack[5].m_obj;
lean_object* v___y_848_ = stack[6].m_obj;
lean_object* v___y_849_ = stack[7].m_obj;
lean_object* v_res_874_;
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_842_, v_a_843_, v_as_844_, v_sz_845_, v_i_846_, v_b_847_, v___y_848_, v___y_849_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___boxed(lean_object* v___x_875_, lean_object* v_a_876_, lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___x_11847__boxed_884_; size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v___x_11847__boxed_884_ = lean_unbox(v___x_875_);
v_sz_boxed_885_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_886_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_11847__boxed_884_, v_a_876_, v_as_877_, v_sz_boxed_885_, v_i_boxed_886_, v_b_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_as_877_);
return v_res_887_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(uint8_t v___x_888_, lean_object* v_a_889_, lean_object* v_as_890_, size_t v_sz_891_, size_t v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_892_, v_sz_891_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_a_889_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_b_893_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_907_; 
lean_dec_ref(v_b_893_);
v___x_899_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_900_ = lean_box(0);
v___f_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_902_ = lean_box(v___x_888_);
v___x_903_ = lean_box(v___x_897_);
lean_inc(v_a_889_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_904_, 0, v___x_899_);
lean_closure_set(v___f_904_, 1, v___x_902_);
lean_closure_set(v___f_904_, 2, v_a_889_);
lean_closure_set(v___f_904_, 3, v___x_900_);
lean_closure_set(v___f_904_, 4, v___x_903_);
v___x_905_ = lean_box(0);
v_a_906_ = lean_array_uget_borrowed(v_as_890_, v_i_892_);
lean_inc(v_a_906_);
v___x_907_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_904_, v___f_901_, v___x_905_, v_a_906_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_892_, v___x_909_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_888_, v_a_889_, v_as_890_, v_sz_891_, v___x_910_, v___x_908_, v___y_894_, v___y_895_);
return v___x_911_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_889_);
v_a_912_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_907_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_888_ = stack[0].m_num;
lean_object* v_a_889_ = stack[1].m_obj;
lean_object* v_as_890_ = stack[2].m_obj;
size_t v_sz_891_ = stack[3].m_num;
size_t v_i_892_ = stack[4].m_num;
lean_object* v_b_893_ = stack[5].m_obj;
lean_object* v___y_894_ = stack[6].m_obj;
lean_object* v___y_895_ = stack[7].m_obj;
lean_object* v_res_920_;
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_888_, v_a_889_, v_as_890_, v_sz_891_, v_i_892_, v_b_893_, v___y_894_, v___y_895_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___boxed(lean_object* v___x_921_, lean_object* v_a_922_, lean_object* v_as_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___x_11954__boxed_930_; size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v___x_11954__boxed_930_ = lean_unbox(v___x_921_);
v_sz_boxed_931_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_932_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_11954__boxed_930_, v_a_922_, v_as_923_, v_sz_boxed_931_, v_i_boxed_932_, v_b_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_as_923_);
return v_res_933_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(uint8_t v___x_937_, lean_object* v_a_938_, lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_941_, v_sz_940_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v_a_938_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_942_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___x_956_; 
lean_dec_ref(v_b_942_);
v___x_948_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_949_ = lean_box(0);
v___f_950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_951_ = lean_box(v___x_937_);
v___x_952_ = lean_box(v___x_946_);
lean_inc(v_a_938_);
v___f_953_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_953_, 0, v___x_948_);
lean_closure_set(v___f_953_, 1, v___x_951_);
lean_closure_set(v___f_953_, 2, v_a_938_);
lean_closure_set(v___f_953_, 3, v___x_949_);
lean_closure_set(v___f_953_, 4, v___x_952_);
v___x_954_ = lean_box(0);
v_a_955_ = lean_array_uget_borrowed(v_as_939_, v_i_941_);
lean_inc(v_a_955_);
v___x_956_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_953_, v___f_950_, v___x_954_, v_a_955_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; size_t v___x_958_; size_t v___x_959_; 
lean_dec_ref_known(v___x_956_, 1);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_941_, v___x_958_);
v_i_941_ = v___x_959_;
v_b_942_ = v___x_957_;
goto _start;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_a_938_);
v_a_961_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_956_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_937_ = stack[0].m_num;
lean_object* v_a_938_ = stack[1].m_obj;
lean_object* v_as_939_ = stack[2].m_obj;
size_t v_sz_940_ = stack[3].m_num;
size_t v_i_941_ = stack[4].m_num;
lean_object* v_b_942_ = stack[5].m_obj;
lean_object* v___y_943_ = stack[6].m_obj;
lean_object* v___y_944_ = stack[7].m_obj;
lean_object* v_res_969_;
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_937_, v_a_938_, v_as_939_, v_sz_940_, v_i_941_, v_b_942_, v___y_943_, v___y_944_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___boxed(lean_object* v___x_970_, lean_object* v_a_971_, lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v___x_12054__boxed_979_; size_t v_sz_boxed_980_; size_t v_i_boxed_981_; lean_object* v_res_982_; 
v___x_12054__boxed_979_ = lean_unbox(v___x_970_);
v_sz_boxed_980_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_981_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_12054__boxed_979_, v_a_971_, v_as_972_, v_sz_boxed_980_, v_i_boxed_981_, v_b_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
return v_res_982_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(uint8_t v___x_983_, lean_object* v_a_984_, lean_object* v_as_985_, size_t v_sz_986_, size_t v_i_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_987_, v_sz_986_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v_a_984_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_b_988_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_b_988_);
v___x_994_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_995_ = lean_box(0);
v___f_996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_997_ = lean_box(v___x_983_);
v___x_998_ = lean_box(v___x_992_);
lean_inc(v_a_984_);
v___f_999_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_999_, 0, v___x_994_);
lean_closure_set(v___f_999_, 1, v___x_997_);
lean_closure_set(v___f_999_, 2, v_a_984_);
lean_closure_set(v___f_999_, 3, v___x_995_);
lean_closure_set(v___f_999_, 4, v___x_998_);
v___x_1000_ = lean_box(0);
v_a_1001_ = lean_array_uget_borrowed(v_as_985_, v_i_987_);
lean_inc(v_a_1001_);
v___x_1002_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_999_, v___f_996_, v___x_1000_, v_a_1001_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref_known(v___x_1002_, 1);
v___x_1003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_987_, v___x_1004_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_983_, v_a_984_, v_as_985_, v_sz_986_, v___x_1005_, v___x_1003_, v___y_989_, v___y_990_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_984_);
v_a_1007_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1002_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_983_ = stack[0].m_num;
lean_object* v_a_984_ = stack[1].m_obj;
lean_object* v_as_985_ = stack[2].m_obj;
size_t v_sz_986_ = stack[3].m_num;
size_t v_i_987_ = stack[4].m_num;
lean_object* v_b_988_ = stack[5].m_obj;
lean_object* v___y_989_ = stack[6].m_obj;
lean_object* v___y_990_ = stack[7].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_983_, v_a_984_, v_as_985_, v_sz_986_, v_i_987_, v_b_988_, v___y_989_, v___y_990_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17___boxed(lean_object* v___x_1016_, lean_object* v_a_1017_, lean_object* v_as_1018_, lean_object* v_sz_1019_, lean_object* v_i_1020_, lean_object* v_b_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v___x_12157__boxed_1025_; size_t v_sz_boxed_1026_; size_t v_i_boxed_1027_; lean_object* v_res_1028_; 
v___x_12157__boxed_1025_ = lean_unbox(v___x_1016_);
v_sz_boxed_1026_ = lean_unbox_usize(v_sz_1019_);
lean_dec(v_sz_1019_);
v_i_boxed_1027_ = lean_unbox_usize(v_i_1020_);
lean_dec(v_i_1020_);
v_res_1028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_12157__boxed_1025_, v_a_1017_, v_as_1018_, v_sz_boxed_1026_, v_i_boxed_1027_, v_b_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_as_1018_);
return v_res_1028_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(lean_object* v_init_1029_, uint8_t v___x_1030_, lean_object* v_a_1031_, lean_object* v_n_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
if (lean_obj_tag(v_n_1032_) == 0)
{
lean_object* v_cs_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v_cs_1037_ = lean_ctor_get(v_n_1032_, 0);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_b_1033_);
v_sz_1040_ = lean_array_size(v_cs_1037_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1029_, v___x_1030_, v_a_1031_, v_cs_1037_, v_sz_1040_, v___x_1041_, v___x_1039_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1057_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1057_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1057_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_fst_1047_; 
v_fst_1047_ = lean_ctor_get(v_a_1043_, 0);
if (lean_obj_tag(v_fst_1047_) == 0)
{
lean_object* v_snd_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v_snd_1048_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_snd_1048_);
lean_dec(v_a_1043_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_snd_1048_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v_val_1053_; lean_object* v___x_1055_; 
lean_inc_ref(v_fst_1047_);
lean_dec(v_a_1043_);
v_val_1053_ = lean_ctor_get(v_fst_1047_, 0);
lean_inc(v_val_1053_);
lean_dec_ref_known(v_fst_1047_, 1);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_val_1053_);
v___x_1055_ = v___x_1045_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_val_1053_);
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
v_a_1058_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1042_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1042_);
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
lean_object* v_vs_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v_vs_1066_ = lean_ctor_get(v_n_1032_, 0);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_b_1033_);
v_sz_1069_ = lean_array_size(v_vs_1066_);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_1030_, v_a_1031_, v_vs_1066_, v_sz_1069_, v___x_1070_, v___x_1068_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1086_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_fst_1076_; 
v_fst_1076_ = lean_ctor_get(v_a_1072_, 0);
if (lean_obj_tag(v_fst_1076_) == 0)
{
lean_object* v_snd_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_snd_1077_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_snd_1077_);
lean_dec(v_a_1072_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_snd_1077_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v_val_1082_; lean_object* v___x_1084_; 
lean_inc_ref(v_fst_1076_);
lean_dec(v_a_1072_);
v_val_1082_ = lean_ctor_get(v_fst_1076_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v_fst_1076_, 1);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_val_1082_);
v___x_1084_ = v___x_1074_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_val_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1071_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1071_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1029_ = stack[0].m_obj;
uint8_t v___x_1030_ = stack[1].m_num;
lean_object* v_a_1031_ = stack[2].m_obj;
lean_object* v_n_1032_ = stack[3].m_obj;
lean_object* v_b_1033_ = stack[4].m_obj;
lean_object* v___y_1034_ = stack[5].m_obj;
lean_object* v___y_1035_ = stack[6].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1029_, v___x_1030_, v_a_1031_, v_n_1032_, v_b_1033_, v___y_1034_, v___y_1035_);
stack->m_obj
 = v_res_1095_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(lean_object* v_init_1096_, uint8_t v___x_1097_, lean_object* v_a_1098_, lean_object* v_as_1099_, size_t v_sz_1100_, size_t v_i_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_usize_dec_lt(v_i_1101_, v_sz_1100_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_dec(v_a_1098_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_b_1102_);
return v___x_1107_;
}
else
{
lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1142_; 
v_snd_1108_ = lean_ctor_get(v_b_1102_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_b_1102_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v_b_1102_, 0);
lean_dec(v_unused_1143_);
v___x_1110_ = v_b_1102_;
v_isShared_1111_ = v_isSharedCheck_1142_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_dec(v_b_1102_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1142_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(0);
v_a_1113_ = lean_array_uget_borrowed(v_as_1099_, v_i_1101_);
lean_inc(v_snd_1108_);
lean_inc(v_a_1098_);
v___x_1114_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1096_, v___x_1097_, v_a_1098_, v_a_1113_, v_snd_1108_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1133_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1133_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1133_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
if (lean_obj_tag(v_a_1115_) == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec(v_a_1098_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_a_1115_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1119_);
v___x_1121_ = v___x_1110_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_snd_1108_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; 
lean_del_object(v___x_1117_);
lean_dec(v_snd_1108_);
v_a_1126_ = lean_ctor_get(v_a_1115_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v_a_1115_, 1);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_a_1126_);
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1128_ = v___x_1110_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_a_1126_);
v___x_1128_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
size_t v___x_1129_; size_t v___x_1130_; 
v___x_1129_ = ((size_t)1ULL);
v___x_1130_ = lean_usize_add(v_i_1101_, v___x_1129_);
v_i_1101_ = v___x_1130_;
v_b_1102_ = v___x_1128_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_del_object(v___x_1110_);
lean_dec(v_snd_1108_);
lean_dec(v_a_1098_);
v_a_1134_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1114_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1114_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1096_ = stack[0].m_obj;
uint8_t v___x_1097_ = stack[1].m_num;
lean_object* v_a_1098_ = stack[2].m_obj;
lean_object* v_as_1099_ = stack[3].m_obj;
size_t v_sz_1100_ = stack[4].m_num;
size_t v_i_1101_ = stack[5].m_num;
lean_object* v_b_1102_ = stack[6].m_obj;
lean_object* v___y_1103_ = stack[7].m_obj;
lean_object* v___y_1104_ = stack[8].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1096_, v___x_1097_, v_a_1098_, v_as_1099_, v_sz_1100_, v_i_1101_, v_b_1102_, v___y_1103_, v___y_1104_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16___boxed(lean_object* v_init_1145_, lean_object* v___x_1146_, lean_object* v_a_1147_, lean_object* v_as_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v___x_12249__boxed_1155_; size_t v_sz_boxed_1156_; size_t v_i_boxed_1157_; lean_object* v_res_1158_; 
v___x_12249__boxed_1155_ = lean_unbox(v___x_1146_);
v_sz_boxed_1156_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1157_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1145_, v___x_12249__boxed_1155_, v_a_1147_, v_as_1148_, v_sz_boxed_1156_, v_i_boxed_1157_, v_b_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_as_1148_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12___boxed(lean_object* v_init_1159_, lean_object* v___x_1160_, lean_object* v_a_1161_, lean_object* v_n_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v___x_12270__boxed_1167_; lean_object* v_res_1168_; 
v___x_12270__boxed_1167_ = lean_unbox(v___x_1160_);
v_res_1168_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1159_, v___x_12270__boxed_1167_, v_a_1161_, v_n_1162_, v_b_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_n_1162_);
return v_res_1168_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(uint8_t v___x_1169_, lean_object* v_a_1170_, lean_object* v_t_1171_, lean_object* v_init_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_root_1176_; lean_object* v_tail_1177_; lean_object* v___x_1178_; 
v_root_1176_ = lean_ctor_get(v_t_1171_, 0);
v_tail_1177_ = lean_ctor_get(v_t_1171_, 1);
lean_inc(v_a_1170_);
v___x_1178_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1172_, v___x_1169_, v_a_1170_, v_root_1176_, v_init_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1215_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1215_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1215_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
if (lean_obj_tag(v_a_1179_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; 
lean_dec(v_a_1170_);
v_a_1183_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v_a_1179_, 1);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_a_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
lean_del_object(v___x_1181_);
v_a_1187_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_a_1179_, 1);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v_a_1187_);
v_sz_1190_ = lean_array_size(v_tail_1177_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_1169_, v_a_1170_, v_tail_1177_, v_sz_1190_, v___x_1191_, v___x_1189_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1206_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1206_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1206_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fst_1197_; 
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
if (lean_obj_tag(v_fst_1197_) == 0)
{
lean_object* v_snd_1198_; lean_object* v___x_1200_; 
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
lean_inc(v_snd_1198_);
lean_dec(v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_snd_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_snd_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1204_; 
lean_inc_ref(v_fst_1197_);
lean_dec(v_a_1193_);
v_val_1202_ = lean_ctor_get(v_fst_1197_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v_fst_1197_, 1);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_val_1202_);
v___x_1204_ = v___x_1195_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_val_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1192_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1192_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1170_);
v_a_1216_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1178_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1178_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1169_ = stack[0].m_num;
lean_object* v_a_1170_ = stack[1].m_obj;
lean_object* v_t_1171_ = stack[2].m_obj;
lean_object* v_init_1172_ = stack[3].m_obj;
lean_object* v___y_1173_ = stack[4].m_obj;
lean_object* v___y_1174_ = stack[5].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_1169_, v_a_1170_, v_t_1171_, v_init_1172_, v___y_1173_, v___y_1174_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8___boxed(lean_object* v___x_1225_, lean_object* v_a_1226_, lean_object* v_t_1227_, lean_object* v_init_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_12564__boxed_1232_; lean_object* v_res_1233_; 
v___x_12564__boxed_1232_ = lean_unbox(v___x_1225_);
v_res_1233_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_12564__boxed_1232_, v_a_1226_, v_t_1227_, v_init_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_t_1227_);
return v_res_1233_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(lean_object* v_o_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_env_1239_; lean_object* v___x_1240_; lean_object* v_toEnvExtension_1241_; lean_object* v_asyncMode_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v_merged_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1254_; 
v___x_1237_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1238_ = lean_st_ref_get(v___y_1235_);
v_env_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_env_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1241_ = lean_ctor_get(v___x_1240_, 0);
v_asyncMode_1242_ = lean_ctor_get(v_toEnvExtension_1241_, 2);
v___x_1243_ = lean_box(0);
v___x_1244_ = 0;
v___x_1245_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1237_, v___x_1240_, v_env_1239_, v_asyncMode_1242_, v___x_1243_, v___x_1244_);
v_merged_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1245_, 1);
lean_dec(v_unused_1255_);
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_merged_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_merged_1246_);
lean_ctor_set(v___x_1248_, 0, v_o_1234_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_o_1234_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_merged_1246_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1234_ = stack[0].m_obj;
lean_object* v___y_1235_ = stack[1].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1234_, v___y_1235_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1257_, v___y_1258_);
lean_dec(v___y_1258_);
return v_res_1260_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_scopes_1266_; lean_object* v___x_1267_; lean_object* v_opts_1268_; lean_object* v___x_1269_; 
v___x_1264_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1265_ = lean_st_ref_get(v___y_1262_);
v_scopes_1266_ = lean_ctor_get(v___x_1265_, 2);
lean_inc(v_scopes_1266_);
lean_dec(v___x_1265_);
v___x_1267_ = l_List_head_x21___redArg(v___x_1264_, v_scopes_1266_);
lean_dec(v_scopes_1266_);
v_opts_1268_ = lean_ctor_get(v___x_1267_, 1);
lean_inc_ref(v_opts_1268_);
lean_dec(v___x_1267_);
v___x_1269_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_opts_1268_, v___y_1262_);
return v___x_1269_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1261_ = stack[0].m_obj;
lean_object* v___y_1262_ = stack[1].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1261_, v___y_1262_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1274_;
}
}
lean_object* l_Lean_Linter_Coe_coeLinter___lam__0(lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1279_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1277_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1276_, v___y_1277_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_1284_ = l_Lean_Linter_getLinterValue(v___x_1283_, v_a_1282_);
lean_dec(v_a_1282_);
v___x_1285_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1277_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = lean_box(0);
v___x_1288_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_1284_, v_a_1280_, v_a_1286_, v___x_1287_, v___y_1276_, v___y_1277_);
lean_dec(v_a_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___x_1288_, 0);
lean_dec(v_unused_1296_);
v___x_1290_ = v___x_1288_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v___x_1288_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1287_);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1287_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
return v___x_1288_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_Coe_coeLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1275_ = stack[0].m_obj;
lean_object* v___y_1276_ = stack[1].m_obj;
lean_object* v___y_1277_ = stack[2].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_1275_, v___y_1276_, v___y_1277_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0___boxed(lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v_x_1298_);
return v_res_1302_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object* v_o_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1314_, v___y_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1314_ = stack[0].m_obj;
lean_object* v___y_1315_ = stack[1].m_obj;
lean_object* v___y_1316_ = stack[2].m_obj;
lean_object* v_res_1319_;
v_res_1319_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_1314_, v___y_1315_, v___y_1316_);
stack->m_obj
 = v_res_1319_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object* v_o_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1324_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(uint8_t v___x_1325_, lean_object* v_i_1326_, lean_object* v_a_1327_, lean_object* v_as_1328_, lean_object* v_as_x27_1329_, lean_object* v_b_1330_, lean_object* v_a_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_1325_, v_i_1326_, v_a_1327_, v_as_x27_1329_, v_b_1330_, v___y_1332_, v___y_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1325_ = stack[0].m_num;
lean_object* v_i_1326_ = stack[1].m_obj;
lean_object* v_a_1327_ = stack[2].m_obj;
lean_object* v_as_1328_ = stack[3].m_obj;
lean_object* v_as_x27_1329_ = stack[4].m_obj;
lean_object* v_b_1330_ = stack[5].m_obj;
lean_object* v___y_1332_ = stack[7].m_obj;
lean_object* v___y_1333_ = stack[8].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(v___x_1325_, v_i_1326_, v_a_1327_, v_as_1328_, v_as_x27_1329_, v_b_1330_, lean_box(0), v___y_1332_, v___y_1333_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object* v___x_1337_, lean_object* v_i_1338_, lean_object* v_a_1339_, lean_object* v_as_1340_, lean_object* v_as_x27_1341_, lean_object* v_b_1342_, lean_object* v_a_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v___x_12943__boxed_1347_; lean_object* v_res_1348_; 
v___x_12943__boxed_1347_ = lean_unbox(v___x_1337_);
v_res_1348_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(v___x_12943__boxed_1347_, v_i_1338_, v_a_1339_, v_as_1340_, v_as_x27_1341_, v_b_1342_, v_a_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_as_x27_1341_);
lean_dec(v_as_1340_);
lean_dec(v_a_1339_);
return v_res_1348_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(lean_object* v_msgData_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_1349_, v___y_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1349_ = stack[0].m_obj;
lean_object* v___y_1350_ = stack[1].m_obj;
lean_object* v___y_1351_ = stack[2].m_obj;
lean_object* v_res_1354_;
v_res_1354_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(v_msgData_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1354_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(v_msgData_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1359_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_object* v_00_u03b1_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_1361_, v___y_1362_, v___y_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1361_ = stack[1].m_obj;
lean_object* v___y_1362_ = stack[2].m_obj;
lean_object* v___y_1363_ = stack[3].m_obj;
lean_object* v_res_1366_;
v_res_1366_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_box(0), v_msg_1361_, v___y_1362_, v___y_1363_);
stack->m_obj
 = v_res_1366_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_msg_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(v_00_u03b1_1367_, v_msg_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1372_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_object* v_00_u03b1_1373_, lean_object* v_preNode_1374_, lean_object* v_postNode_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_1374_, v_postNode_1375_, v_x_1376_, v_x_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1374_ = stack[1].m_obj;
lean_object* v_postNode_1375_ = stack[2].m_obj;
lean_object* v_x_1376_ = stack[3].m_obj;
lean_object* v_x_1377_ = stack[4].m_obj;
lean_object* v___y_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_box(0), v_preNode_1374_, v_postNode_1375_, v_x_1376_, v_x_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_preNode_1384_, lean_object* v_postNode_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_00_u03b1_1383_, v_preNode_1384_, v_postNode_1385_, v_x_1386_, v_x_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1391_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1392_, lean_object* v_preNode_1393_, lean_object* v_postNode_1394_, lean_object* v___x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_1393_, v_postNode_1394_, v___x_1395_, v_x_1396_, v_x_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1393_ = stack[1].m_obj;
lean_object* v_postNode_1394_ = stack[2].m_obj;
lean_object* v___x_1395_ = stack[3].m_obj;
lean_object* v_x_1396_ = stack[4].m_obj;
lean_object* v_x_1397_ = stack[5].m_obj;
lean_object* v___y_1398_ = stack[6].m_obj;
lean_object* v___y_1399_ = stack[7].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_box(0), v_preNode_1393_, v_postNode_1394_, v___x_1395_, v_x_1396_, v_x_1397_, v___y_1398_, v___y_1399_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_preNode_1404_, lean_object* v_postNode_1405_, lean_object* v___x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(v_00_u03b1_1403_, v_preNode_1404_, v_postNode_1405_, v___x_1406_, v_x_1407_, v_x_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1412_;
}
}
lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lean_Linter_Coe_coeLinter));
v___x_1415_ = l_Lean_Elab_Command_addLinter(v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1416_;
v_res_1416_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
return v_res_1418_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = initialize_Lean_Elab_InfoTree_Util(builtin);
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
