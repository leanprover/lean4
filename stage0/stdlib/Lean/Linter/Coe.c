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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_getOptions_50_; lean_object* v_toPure_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toApplicative_48_);
v_toBind_49_ = lean_ctor_get(v_inst_46_, 1);
lean_inc(v_toBind_49_);
lean_dec_ref(v_inst_46_);
v_getOptions_50_ = lean_ctor_get(v_inst_47_, 0);
lean_inc(v_getOptions_50_);
lean_dec_ref(v_inst_47_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc(v_toPure_51_);
lean_dec_ref(v_toApplicative_48_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_52_, 0, v_toPure_51_);
v___x_53_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v_getOptions_50_, v___f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions(lean_object* v_m_54_, lean_object* v_inst_55_, lean_object* v_inst_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Linter_Coe_shouldWarnOnDeprecatedCoercions___redArg(v_inst_55_, v_inst_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v_mainModule_76_; lean_object* v___x_77_; 
v___x_73_ = lean_st_ref_get(v___y_71_);
v_env_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_env_74_);
lean_dec(v___x_73_);
v___x_75_ = l_Lean_Environment_header(v_env_74_);
lean_dec_ref(v_env_74_);
v_mainModule_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_mainModule_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_mainModule_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg___boxed(lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_78_);
lean_dec(v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___boxed(lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0(v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_infoState_92_; lean_object* v_trees_93_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_infoState_92_ = lean_ctor_get(v___x_91_, 8);
lean_inc_ref(v_infoState_92_);
lean_dec(v___x_91_);
v_trees_93_ = lean_ctor_get(v_infoState_92_, 2);
lean_inc_ref(v_trees_93_);
lean_dec_ref(v_infoState_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_trees_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg___boxed(lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_95_);
lean_dec(v___y_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___boxed(lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2(v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_105_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_instMonadEIO___redArg();
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_toApplicative_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_146_; 
v___x_113_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__0);
v___x_114_ = l_StateRefT_x27_instMonad___redArg(v___x_113_);
v_toApplicative_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v___x_114_, 1);
lean_dec(v_unused_147_);
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_146_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_toApplicative_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_146_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_toFunctor_119_; lean_object* v_toSeq_120_; lean_object* v_toSeqLeft_121_; lean_object* v_toSeqRight_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_144_; 
v_toFunctor_119_ = lean_ctor_get(v_toApplicative_115_, 0);
v_toSeq_120_ = lean_ctor_get(v_toApplicative_115_, 2);
v_toSeqLeft_121_ = lean_ctor_get(v_toApplicative_115_, 3);
v_toSeqRight_122_ = lean_ctor_get(v_toApplicative_115_, 4);
v_isSharedCheck_144_ = !lean_is_exclusive(v_toApplicative_115_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_dec(v_unused_145_);
v___x_124_ = v_toApplicative_115_;
v_isShared_125_ = v_isSharedCheck_144_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_toSeqRight_122_);
lean_inc(v_toSeqLeft_121_);
lean_inc(v_toSeq_120_);
lean_inc(v_toFunctor_119_);
lean_dec(v_toApplicative_115_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_144_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_135_; 
v___f_126_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__1));
v___f_127_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___closed__2));
lean_inc_ref(v_toFunctor_119_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_128_, 0, v_toFunctor_119_);
v___f_129_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_129_, 0, v_toFunctor_119_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___f_128_);
lean_ctor_set(v___x_130_, 1, v___f_129_);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_131_, 0, v_toSeqRight_122_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_132_, 0, v_toSeqLeft_121_);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_133_, 0, v_toSeq_120_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 4, v___f_131_);
lean_ctor_set(v___x_124_, 3, v___f_132_);
lean_ctor_set(v___x_124_, 2, v___f_133_);
lean_ctor_set(v___x_124_, 1, v___f_126_);
lean_ctor_set(v___x_124_, 0, v___x_130_);
v___x_135_ = v___x_124_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___f_126_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v___f_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v___f_132_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v___f_131_);
v___x_135_ = v_reuseFailAlloc_143_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___f_127_);
lean_ctor_set(v___x_117_, 0, v___x_135_);
v___x_137_ = v___x_117_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___f_127_);
v___x_137_ = v_reuseFailAlloc_142_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_8356__overap_140_; lean_object* v___x_141_; 
v___x_138_ = lean_box(0);
v___x_139_ = l_instInhabitedOfMonad___redArg(v___x_137_, v___x_138_);
v___x_8356__overap_140_ = lean_panic_fn_borrowed(v___x_139_, v_msg_109_);
lean_dec(v___x_139_);
lean_inc(v___y_111_);
lean_inc_ref(v___y_110_);
v___x_141_ = lean_apply_3(v___x_8356__overap_140_, v___y_110_, v___y_111_, lean_box(0));
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_152_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__2));
v___x_157_ = lean_unsigned_to_nat(21u);
v___x_158_ = lean_unsigned_to_nat(65u);
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__1));
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__0));
v___x_161_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_159_, v___x_158_, v___x_157_, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(lean_object* v_preNode_162_, lean_object* v_postNode_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
switch(lean_obj_tag(v_x_165_))
{
case 0:
{
lean_object* v_i_169_; lean_object* v_t_170_; lean_object* v___x_171_; 
v_i_169_ = lean_ctor_get(v_x_165_, 0);
lean_inc_ref(v_i_169_);
v_t_170_ = lean_ctor_get(v_x_165_, 1);
lean_inc_ref(v_t_170_);
lean_dec_ref_known(v_x_165_, 2);
v___x_171_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_169_, v_x_164_);
v_x_164_ = v___x_171_;
v_x_165_ = v_t_170_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref_known(v_x_165_, 2);
lean_dec_ref(v_postNode_163_);
lean_dec_ref(v_preNode_162_);
v___x_173_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___closed__3);
v___x_174_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v___x_173_, v___y_166_, v___y_167_);
return v___x_174_;
}
else
{
lean_object* v_i_175_; lean_object* v_children_176_; lean_object* v_val_177_; lean_object* v___x_178_; 
v_i_175_ = lean_ctor_get(v_x_165_, 0);
lean_inc_ref_n(v_i_175_, 2);
v_children_176_ = lean_ctor_get(v_x_165_, 1);
lean_inc_ref_n(v_children_176_, 2);
lean_dec_ref_known(v_x_165_, 2);
v_val_177_ = lean_ctor_get(v_x_164_, 0);
lean_inc_n(v_val_177_, 2);
lean_inc_ref(v_preNode_162_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_178_ = lean_apply_6(v_preNode_162_, v_val_177_, v_i_175_, v_children_176_, v___y_166_, v___y_167_, lean_box(0));
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; uint8_t v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_preNode_162_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_x_164_, 0);
lean_dec(v_unused_206_);
v___x_182_ = v_x_164_;
v_isShared_183_ = v_isSharedCheck_205_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_x_164_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_205_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(0);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_185_ = lean_apply_7(v_postNode_163_, v_val_177_, v_i_175_, v_children_176_, v___x_184_, v___y_166_, v___y_167_, lean_box(0));
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v_a_186_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_del_object(v___x_182_);
v_a_197_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_185_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_185_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = l_Lean_Elab_Info_updateContext_x3f(v_x_164_, v_i_175_);
v___x_208_ = l_Lean_PersistentArray_toList___redArg(v_children_176_);
v___x_209_ = lean_box(0);
lean_inc_ref(v_postNode_163_);
v___x_210_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_162_, v_postNode_163_, v___x_207_, v___x_208_, v___x_209_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_212_ = lean_apply_7(v_postNode_163_, v_val_177_, v_i_175_, v_children_176_, v_a_211_, v___y_166_, v___y_167_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_221_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_221_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_a_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_a_222_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_212_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_212_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_val_177_);
lean_dec_ref(v_children_176_);
lean_dec_ref(v_i_175_);
lean_dec_ref(v_postNode_163_);
v_a_230_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_210_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_210_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_val_177_);
lean_dec_ref(v_children_176_);
lean_dec_ref_known(v_x_164_, 1);
lean_dec_ref(v_i_175_);
lean_dec_ref(v_postNode_163_);
lean_dec_ref(v_preNode_162_);
v_a_238_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_178_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_178_);
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
}
default: 
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_x_164_);
lean_dec_ref(v_postNode_163_);
lean_dec_ref(v_preNode_162_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v_x_165_, 0);
lean_dec(v_unused_254_);
v___x_247_ = v_x_165_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_x_165_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_box(0);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 0);
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(lean_object* v_preNode_255_, lean_object* v_postNode_256_, lean_object* v___x_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_257_);
lean_dec_ref(v_postNode_256_);
lean_dec_ref(v_preNode_255_);
v___x_263_ = l_List_reverse___redArg(v_x_259_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v_head_265_; lean_object* v_tail_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_284_; 
v_head_265_ = lean_ctor_get(v_x_258_, 0);
v_tail_266_ = lean_ctor_get(v_x_258_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_284_ == 0)
{
v___x_268_ = v_x_258_;
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_tail_266_);
lean_inc(v_head_265_);
lean_dec(v_x_258_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; 
lean_inc(v___x_257_);
lean_inc_ref(v_postNode_256_);
lean_inc_ref(v_preNode_255_);
v___x_270_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_255_, v_postNode_256_, v___x_257_, v_head_265_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v_x_259_);
lean_ctor_set(v___x_268_, 0, v_a_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_271_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_x_259_);
v___x_273_ = v_reuseFailAlloc_275_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v_x_258_ = v_tail_266_;
v_x_259_ = v___x_273_;
goto _start;
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_del_object(v___x_268_);
lean_dec(v_tail_266_);
lean_dec(v_x_259_);
lean_dec(v___x_257_);
lean_dec_ref(v_postNode_256_);
lean_dec_ref(v_preNode_255_);
v_a_276_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_270_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_270_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_preNode_285_, lean_object* v_postNode_286_, lean_object* v___x_287_, lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_285_, v_postNode_286_, v___x_287_, v_x_288_, v_x_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg___boxed(lean_object* v_preNode_294_, lean_object* v_postNode_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_294_, v_postNode_295_, v_x_296_, v_x_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(lean_object* v_postNode_302_, lean_object* v_ci_303_, lean_object* v_i_304_, lean_object* v_cs_305_, lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
v___x_310_ = lean_apply_6(v_postNode_302_, v_ci_303_, v_i_304_, v_cs_305_, v___y_307_, v___y_308_, lean_box(0));
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed(lean_object* v_postNode_311_, lean_object* v_ci_312_, lean_object* v_i_313_, lean_object* v_cs_314_, lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0(v_postNode_311_, v_ci_312_, v_i_313_, v_cs_314_, v_x_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v_x_315_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(lean_object* v_preNode_320_, lean_object* v_postNode_321_, lean_object* v_ctx_x3f_322_, lean_object* v_t_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(v___f_327_, 0, v_postNode_321_);
v___x_328_ = lean_box(0);
v___x_329_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_320_, v___f_327_, v_ctx_x3f_322_, v_t_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_337_);
v___x_331_ = v___x_329_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_dec(v___x_329_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_328_);
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_328_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_329_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_329_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7___boxed(lean_object* v_preNode_346_, lean_object* v_postNode_347_, lean_object* v_ctx_x3f_348_, lean_object* v_t_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v_preNode_346_, v_postNode_347_, v_ctx_x3f_348_, v_t_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_354_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_358_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_ctor_set(v___x_360_, 3, v___x_359_);
lean_ctor_set(v___x_360_, 4, v___x_358_);
lean_ctor_set(v___x_360_, 5, v___x_358_);
lean_ctor_set(v___x_360_, 6, v___x_358_);
lean_ctor_set(v___x_360_, 7, v___x_358_);
lean_ctor_set(v___x_360_, 8, v___x_358_);
lean_ctor_set(v___x_360_, 9, v___x_358_);
lean_ctor_set(v___x_360_, 10, v___x_358_);
lean_ctor_set(v___x_360_, 11, v___x_357_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(32u);
v___x_362_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_364_ = ((size_t)5ULL);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_unsigned_to_nat(32u);
v___x_367_ = lean_mk_empty_array_with_capacity(v___x_366_);
v___x_368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__3);
v___x_369_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_365_);
lean_ctor_set(v___x_369_, 3, v___x_365_);
lean_ctor_set_usize(v___x_369_, 4, v___x_364_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = lean_box(1);
v___x_371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__4);
v___x_372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__1);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(lean_object* v_msgData_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_env_378_; uint8_t v___x_379_; lean_object* v_env_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_scopes_383_; lean_object* v___x_384_; lean_object* v_opts_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_377_ = lean_st_ref_get(v___y_375_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_env_378_);
lean_dec(v___x_377_);
v___x_379_ = 0;
v_env_380_ = l_Lean_Environment_setRecordingDeps(v_env_378_, v___x_379_);
v___x_381_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_382_ = lean_st_ref_get(v___y_375_);
v_scopes_383_ = lean_ctor_get(v___x_382_, 2);
lean_inc(v_scopes_383_);
lean_dec(v___x_382_);
v___x_384_ = l_List_head_x21___redArg(v___x_381_, v_scopes_383_);
lean_dec(v_scopes_383_);
v_opts_385_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_opts_385_);
lean_dec(v___x_384_);
v___x_386_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__2);
v___x_387_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___closed__5);
v___x_388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_388_, 0, v_env_380_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_ctor_set(v___x_388_, 3, v_opts_385_);
v___x_389_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_msgData_374_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_391_, v___y_392_);
lean_dec(v___y_392_);
return v_res_394_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(uint8_t v_suppressElabErrors_396_, lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_397_) == 1)
{
lean_object* v_pre_398_; 
v_pre_398_ = lean_ctor_get(v_x_397_, 0);
if (lean_obj_tag(v_pre_398_) == 0)
{
lean_object* v_str_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_str_399_ = lean_ctor_get(v_x_397_, 1);
v___x_400_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___closed__0));
v___x_401_ = lean_string_dec_eq(v_str_399_, v___x_400_);
if (v___x_401_ == 0)
{
return v___x_401_;
}
else
{
return v_suppressElabErrors_396_;
}
}
else
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_404_, lean_object* v_x_405_){
_start:
{
uint8_t v_suppressElabErrors_boxed_406_; uint8_t v_res_407_; lean_object* v_r_408_; 
v_suppressElabErrors_boxed_406_ = lean_unbox(v_suppressElabErrors_404_);
v_res_407_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0(v_suppressElabErrors_boxed_406_, v_x_405_);
lean_dec(v_x_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(lean_object* v_ref_410_, lean_object* v_msgData_411_, uint8_t v_severity_412_, uint8_t v_isSilent_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; uint8_t v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; uint8_t v___y_483_; uint8_t v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v___y_512_; uint8_t v___y_516_; uint8_t v___y_517_; uint8_t v___x_532_; uint8_t v___y_534_; uint8_t v___x_544_; 
v___x_532_ = 2;
v___x_544_ = l_Lean_instBEqMessageSeverity_beq(v_severity_412_, v___x_532_);
if (v___x_544_ == 0)
{
v___y_534_ = v___x_544_;
goto v___jp_533_;
}
else
{
uint8_t v___x_545_; 
lean_inc_ref(v_msgData_411_);
v___x_545_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_411_);
if (v___x_545_ == 0)
{
v___y_534_ = v___x_545_;
goto v___jp_533_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v_msgData_411_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
v___jp_417_:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_Command_getScope___redArg(v___y_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_currNamespace_428_; lean_object* v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v_currNamespace_428_ = lean_ctor_get(v_a_427_, 2);
lean_inc(v_currNamespace_428_);
lean_dec(v_a_427_);
v___x_429_ = l_Lean_Elab_Command_getScope___redArg(v___y_425_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_465_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_465_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_465_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_465_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_openDecls_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_env_439_; lean_object* v_messages_440_; lean_object* v_scopes_441_; lean_object* v_usedQuotCtxts_442_; lean_object* v_nextMacroScope_443_; lean_object* v_maxRecDepth_444_; lean_object* v_ngen_445_; lean_object* v_auxDeclNGen_446_; lean_object* v_infoState_447_; lean_object* v_traceState_448_; lean_object* v_snapshotTasks_449_; lean_object* v_prevLinterStates_450_; lean_object* v_codeQualityEntryTasks_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_464_; 
v_openDecls_434_ = lean_ctor_get(v_a_430_, 3);
lean_inc(v_openDecls_434_);
lean_dec(v_a_430_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_currNamespace_428_);
lean_ctor_set(v___x_435_, 1, v_openDecls_434_);
v___x_436_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___y_424_);
lean_inc_ref(v___y_422_);
lean_inc_ref(v___y_419_);
v___x_437_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_437_, 0, v___y_419_);
lean_ctor_set(v___x_437_, 1, v___y_420_);
lean_ctor_set(v___x_437_, 2, v___y_421_);
lean_ctor_set(v___x_437_, 3, v___y_422_);
lean_ctor_set(v___x_437_, 4, v___x_436_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*5, v___y_418_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*5 + 1, v___y_423_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*5 + 2, v_isSilent_413_);
v___x_438_ = lean_st_ref_take(v___y_425_);
v_env_439_ = lean_ctor_get(v___x_438_, 0);
v_messages_440_ = lean_ctor_get(v___x_438_, 1);
v_scopes_441_ = lean_ctor_get(v___x_438_, 2);
v_usedQuotCtxts_442_ = lean_ctor_get(v___x_438_, 3);
v_nextMacroScope_443_ = lean_ctor_get(v___x_438_, 4);
v_maxRecDepth_444_ = lean_ctor_get(v___x_438_, 5);
v_ngen_445_ = lean_ctor_get(v___x_438_, 6);
v_auxDeclNGen_446_ = lean_ctor_get(v___x_438_, 7);
v_infoState_447_ = lean_ctor_get(v___x_438_, 8);
v_traceState_448_ = lean_ctor_get(v___x_438_, 9);
v_snapshotTasks_449_ = lean_ctor_get(v___x_438_, 10);
v_prevLinterStates_450_ = lean_ctor_get(v___x_438_, 11);
v_codeQualityEntryTasks_451_ = lean_ctor_get(v___x_438_, 12);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_464_ == 0)
{
v___x_453_ = v___x_438_;
v_isShared_454_ = v_isSharedCheck_464_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_codeQualityEntryTasks_451_);
lean_inc(v_prevLinterStates_450_);
lean_inc(v_snapshotTasks_449_);
lean_inc(v_traceState_448_);
lean_inc(v_infoState_447_);
lean_inc(v_auxDeclNGen_446_);
lean_inc(v_ngen_445_);
lean_inc(v_maxRecDepth_444_);
lean_inc(v_nextMacroScope_443_);
lean_inc(v_usedQuotCtxts_442_);
lean_inc(v_scopes_441_);
lean_inc(v_messages_440_);
lean_inc(v_env_439_);
lean_dec(v___x_438_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_464_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_MessageLog_add(v___x_437_, v_messages_440_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_439_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_scopes_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_usedQuotCtxts_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_nextMacroScope_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_maxRecDepth_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_ngen_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_auxDeclNGen_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_traceState_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_snapshotTasks_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 11, v_prevLinterStates_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 12, v_codeQualityEntryTasks_451_);
v___x_458_ = v_reuseFailAlloc_463_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_st_ref_put(v___y_425_, v___x_458_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_455_);
v___x_461_ = v___x_432_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_455_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_currNamespace_428_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
v_a_466_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_429_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_429_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v___y_424_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
v_a_474_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_426_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_426_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
v___jp_482_:
{
lean_object* v_fileName_487_; lean_object* v_fileMap_488_; uint8_t v_suppressElabErrors_489_; lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_fileName_487_ = lean_ctor_get(v___y_414_, 0);
v_fileMap_488_ = lean_ctor_get(v___y_414_, 1);
v_suppressElabErrors_489_ = lean_ctor_get_uint8(v___y_414_, sizeof(void*)*10);
v___x_490_ = lean_box(v_suppressElabErrors_489_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_491_, 0, v___x_490_);
v___x_492_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_411_);
v___x_493_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v___x_492_, v___y_415_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc_ref_n(v_fileMap_488_, 2);
v___x_498_ = l_Lean_FileMap_toPosition(v_fileMap_488_, v___y_485_);
lean_dec(v___y_485_);
v___x_499_ = l_Lean_FileMap_toPosition(v_fileMap_488_, v___y_486_);
lean_dec(v___y_486_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___closed__0));
if (v_suppressElabErrors_489_ == 0)
{
lean_del_object(v___x_496_);
lean_dec_ref(v___f_491_);
v___y_418_ = v___y_483_;
v___y_419_ = v_fileName_487_;
v___y_420_ = v___x_498_;
v___y_421_ = v___x_500_;
v___y_422_ = v___x_501_;
v___y_423_ = v___y_484_;
v___y_424_ = v_a_494_;
v___y_425_ = v___y_415_;
goto v___jp_417_;
}
else
{
uint8_t v___x_502_; 
lean_inc(v_a_494_);
v___x_502_ = l_Lean_MessageData_hasTag(v___f_491_, v_a_494_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec_ref_known(v___x_500_, 1);
lean_dec_ref(v___x_498_);
lean_dec(v_a_494_);
v___x_503_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_del_object(v___x_496_);
v___y_418_ = v___y_483_;
v___y_419_ = v_fileName_487_;
v___y_420_ = v___x_498_;
v___y_421_ = v___x_500_;
v___y_422_ = v___x_501_;
v___y_423_ = v___y_484_;
v___y_424_ = v_a_494_;
v___y_425_ = v___y_415_;
goto v___jp_417_;
}
}
}
}
v___jp_508_:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Syntax_getTailPos_x3f(v___y_510_, v___y_509_);
lean_dec(v___y_510_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_inc(v___y_512_);
v___y_483_ = v___y_509_;
v___y_484_ = v___y_511_;
v___y_485_ = v___y_512_;
v___y_486_ = v___y_512_;
goto v___jp_482_;
}
else
{
lean_object* v_val_514_; 
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v___x_513_, 1);
v___y_483_ = v___y_509_;
v___y_484_ = v___y_511_;
v___y_485_ = v___y_512_;
v___y_486_ = v_val_514_;
goto v___jp_482_;
}
}
v___jp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Elab_Command_getRef___redArg(v___y_414_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_ref_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_ref_520_ = l_Lean_replaceRef(v_ref_410_, v_a_519_);
lean_dec(v_a_519_);
v___x_521_ = l_Lean_Syntax_getPos_x3f(v_ref_520_, v___y_516_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___y_509_ = v___y_516_;
v___y_510_ = v_ref_520_;
v___y_511_ = v___y_517_;
v___y_512_ = v___x_522_;
goto v___jp_508_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_521_, 1);
v___y_509_ = v___y_516_;
v___y_510_ = v_ref_520_;
v___y_511_ = v___y_517_;
v___y_512_ = v_val_523_;
goto v___jp_508_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v_msgData_411_);
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
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_scopes_537_; lean_object* v___x_538_; lean_object* v_opts_539_; uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_535_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_536_ = lean_st_ref_get(v___y_415_);
v_scopes_537_ = lean_ctor_get(v___x_536_, 2);
lean_inc(v_scopes_537_);
lean_dec(v___x_536_);
v___x_538_ = l_List_head_x21___redArg(v___x_535_, v_scopes_537_);
lean_dec(v_scopes_537_);
v_opts_539_ = lean_ctor_get(v___x_538_, 1);
lean_inc_ref(v_opts_539_);
lean_dec(v___x_538_);
v___x_540_ = 1;
v___x_541_ = l_Lean_instBEqMessageSeverity_beq(v_severity_412_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec_ref(v_opts_539_);
v___y_516_ = v___y_534_;
v___y_517_ = v_severity_412_;
goto v___jp_515_;
}
else
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = l_Lean_warningAsError;
v___x_543_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_throwErrorIfErrors_spec__0_spec__1_spec__2(v_opts_539_, v___x_542_);
lean_dec_ref(v_opts_539_);
if (v___x_543_ == 0)
{
v___y_516_ = v___y_534_;
v___y_517_ = v_severity_412_;
goto v___jp_515_;
}
else
{
v___y_516_ = v___y_534_;
v___y_517_ = v___x_532_;
goto v___jp_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7___boxed(lean_object* v_ref_548_, lean_object* v_msgData_549_, lean_object* v_severity_550_, lean_object* v_isSilent_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v_severity_boxed_555_; uint8_t v_isSilent_boxed_556_; lean_object* v_res_557_; 
v_severity_boxed_555_ = lean_unbox(v_severity_550_);
v_isSilent_boxed_556_ = lean_unbox(v_isSilent_551_);
v_res_557_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_548_, v_msgData_549_, v_severity_boxed_555_, v_isSilent_boxed_556_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v_ref_548_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(lean_object* v_ref_558_, lean_object* v_msgData_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = 1;
v___x_564_ = 0;
v___x_565_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7(v_ref_558_, v_msgData_559_, v___x_563_, v___x_564_, v___y_560_, v___y_561_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5___boxed(lean_object* v_ref_566_, lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_ref_566_, v_msgData_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v_ref_566_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__2));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(lean_object* v_linterOption_578_, lean_object* v_stx_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_name_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_602_; 
v_name_584_ = lean_ctor_get(v_linterOption_578_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_linterOption_578_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_linterOption_578_, 1);
lean_dec(v_unused_603_);
v___x_586_ = v_linterOption_578_;
v_isShared_587_ = v_isSharedCheck_602_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_name_584_);
lean_dec(v_linterOption_578_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_602_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__1);
lean_inc(v_name_584_);
v___x_589_ = l_Lean_MessageData_ofName(v_name_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 7);
lean_ctor_set(v___x_586_, 1, v___x_589_);
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_601_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_disable_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_592_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___closed__3);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v_disable_594_ = l_Lean_MessageData_note(v___x_593_);
v___x_595_ = l_Lean_Linter_linterMessageTag;
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v_msg_580_);
lean_ctor_set(v___x_596_, 1, v_disable_594_);
v___x_597_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_598_, 0, v_name_584_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc(v_stx_579_);
v___x_599_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_599_, 0, v_stx_579_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_579_, v___x_599_, v___y_581_, v___y_582_);
lean_dec(v_stx_579_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3___boxed(lean_object* v_linterOption_604_, lean_object* v_stx_605_, lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v_linterOption_604_, v_stx_605_, v_msg_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_610_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(lean_object* v_a_611_, lean_object* v_as_612_, size_t v_i_613_, size_t v_stop_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = lean_usize_dec_eq(v_i_613_, v_stop_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_uget_borrowed(v_as_612_, v_i_613_);
v___x_617_ = lean_name_eq(v_a_611_, v___x_616_);
if (v___x_617_ == 0)
{
size_t v___x_618_; size_t v___x_619_; 
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_613_, v___x_618_);
v_i_613_ = v___x_619_;
goto _start;
}
else
{
return v___x_617_;
}
}
else
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5___boxed(lean_object* v_a_622_, lean_object* v_as_623_, lean_object* v_i_624_, lean_object* v_stop_625_){
_start:
{
size_t v_i_boxed_626_; size_t v_stop_boxed_627_; uint8_t v_res_628_; lean_object* v_r_629_; 
v_i_boxed_626_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_stop_boxed_627_ = lean_unbox_usize(v_stop_625_);
lean_dec(v_stop_625_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_622_, v_as_623_, v_i_boxed_626_, v_stop_boxed_627_);
lean_dec_ref(v_as_623_);
lean_dec(v_a_622_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(lean_object* v_as_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_array_get_size(v_as_630_);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
size_t v___x_635_; size_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = ((size_t)0ULL);
v___x_636_ = lean_usize_of_nat(v___x_633_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4_spec__5(v_a_631_, v_as_630_, v___x_635_, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4___boxed(lean_object* v_as_638_, lean_object* v_a_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v_as_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_as_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__2));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__4));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__6));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__8));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(uint8_t v___x_676_, lean_object* v_i_677_, lean_object* v_a_678_, lean_object* v_as_x27_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
if (lean_obj_tag(v_as_x27_679_) == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v_i_677_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_b_680_);
return v___x_684_;
}
else
{
lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_head_685_ = lean_ctor_get(v_as_x27_679_, 0);
v_tail_686_ = lean_ctor_get(v_as_x27_679_, 1);
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
v___x_689_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__12));
v___x_720_ = lean_name_eq(v_a_678_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = l_Lean_Name_getRoot(v_a_678_);
v___x_722_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__18));
v___x_723_ = l_List_elem___at___00Lean_Elab_Term_levelMVarToParam_spec__0(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
if (v___x_723_ == 0)
{
v___y_691_ = v___y_681_;
v___y_692_ = v___y_682_;
goto v___jp_690_;
}
else
{
goto v___jp_709_;
}
}
else
{
goto v___jp_709_;
}
v___jp_690_:
{
if (v___x_676_ == 0)
{
v_as_x27_679_ = v_tail_686_;
v_b_680_ = v___x_687_;
goto _start;
}
else
{
lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_st_ref_get(v___y_692_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_694_);
v___x_696_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_head_685_);
v___x_697_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_688_, v___x_696_, v_env_695_, v_head_685_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_stx_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref_known(v___x_697_, 1);
v_stx_698_ = lean_ctor_get(v_i_677_, 0);
v___x_699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__1));
v___x_700_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__3);
lean_inc(v_head_685_);
v___x_701_ = l_Lean_MessageData_ofConstName(v_head_685_, v___x_676_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__5);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_699_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_inc(v_stx_698_);
v___x_706_ = l_Lean_Linter_logLint___at___00Lean_Linter_Coe_coeLinter_spec__3(v___x_689_, v_stx_698_, v___x_705_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v_as_x27_679_ = v_tail_686_;
v_b_680_ = v___x_687_;
goto _start;
}
else
{
lean_dec_ref(v_i_677_);
return v___x_706_;
}
}
else
{
lean_dec(v___x_697_);
v_as_x27_679_ = v_tail_686_;
v_b_680_ = v___x_687_;
goto _start;
}
}
}
v___jp_709_:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Linter_Coe_coercionsBannedInCore));
v___x_711_ = l_Array_contains___at___00Lean_Linter_Coe_coeLinter_spec__4(v___x_710_, v_head_685_);
if (v___x_711_ == 0)
{
v___y_691_ = v___y_681_;
v___y_692_ = v___y_682_;
goto v___jp_690_;
}
else
{
lean_object* v_stx_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_stx_712_ = lean_ctor_get(v_i_677_, 0);
v___x_713_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__7);
lean_inc(v_head_685_);
v___x_714_ = l_Lean_MessageData_ofName(v_head_685_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9, &l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___closed__9);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5(v_stx_712_, v___x_717_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_dec_ref_known(v___x_718_, 1);
v___y_691_ = v___y_681_;
v___y_692_ = v___y_682_;
goto v___jp_690_;
}
else
{
lean_dec_ref(v_i_677_);
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg___boxed(lean_object* v___x_724_, lean_object* v_i_725_, lean_object* v_a_726_, lean_object* v_as_x27_727_, lean_object* v_b_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
uint8_t v___x_10989__boxed_732_; lean_object* v_res_733_; 
v___x_10989__boxed_732_ = lean_unbox(v___x_724_);
v_res_733_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_10989__boxed_732_, v_i_725_, v_a_726_, v_as_x27_727_, v_b_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_as_x27_727_);
lean_dec(v_a_726_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(lean_object* v___x_734_, uint8_t v___x_735_, lean_object* v_a_736_, lean_object* v___x_737_, uint8_t v___x_738_, lean_object* v_x_739_, lean_object* v_info_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
if (lean_obj_tag(v_info_740_) == 10)
{
lean_object* v_i_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_774_; 
v_i_745_ = lean_ctor_get(v_info_740_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_info_740_);
if (v_isSharedCheck_774_ == 0)
{
v___x_747_ = v_info_740_;
v_isShared_748_ = v_isSharedCheck_774_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_i_745_);
lean_dec(v_info_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_774_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_value_749_; lean_object* v___x_750_; 
v_value_749_ = lean_ctor_get(v_i_745_, 1);
v___x_750_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_749_, v___x_734_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; 
lean_del_object(v___x_747_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_735_, v_i_745_, v_a_736_, v_val_751_, v___x_737_, v___y_742_, v___y_743_);
lean_dec(v_val_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_752_, 0);
lean_dec(v_unused_761_);
v___x_754_ = v___x_752_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_dec(v___x_752_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = lean_box(v___x_738_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_752_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_752_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v___x_750_);
lean_dec_ref(v_i_745_);
v___x_770_ = lean_box(v___x_738_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 0, v___x_770_);
v___x_772_ = v___x_747_;
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
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_info_740_);
v___x_775_ = lean_box(v___x_738_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed(lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v_a_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v_x_782_, lean_object* v_info_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_11120__boxed_788_; uint8_t v___x_11123__boxed_789_; lean_object* v_res_790_; 
v___x_11120__boxed_788_ = lean_unbox(v___x_778_);
v___x_11123__boxed_789_ = lean_unbox(v___x_781_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1(v___x_777_, v___x_11120__boxed_788_, v_a_779_, v___x_780_, v___x_11123__boxed_789_, v_x_782_, v_info_783_, v_x_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_x_784_);
lean_dec_ref(v_x_782_);
lean_dec(v_a_779_);
lean_dec(v___x_777_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(lean_object* v___x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_791_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0___boxed(lean_object* v___x_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__0(v___x_799_, v_x_800_, v_x_801_, v_x_802_, v_x_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v_x_803_);
lean_dec_ref(v_x_802_);
lean_dec_ref(v_x_801_);
lean_dec_ref(v_x_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(uint8_t v___x_812_, lean_object* v_a_813_, lean_object* v_as_814_, size_t v_sz_815_, size_t v_i_816_, lean_object* v_b_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_lt(v_i_816_, v_sz_815_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v_a_813_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_b_817_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_831_; 
lean_dec_ref(v_b_817_);
v___x_823_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_824_ = lean_box(0);
v___f_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_826_ = lean_box(v___x_812_);
v___x_827_ = lean_box(v___x_821_);
lean_inc(v_a_813_);
v___f_828_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_828_, 0, v___x_823_);
lean_closure_set(v___f_828_, 1, v___x_826_);
lean_closure_set(v___f_828_, 2, v_a_813_);
lean_closure_set(v___f_828_, 3, v___x_824_);
lean_closure_set(v___f_828_, 4, v___x_827_);
v___x_829_ = lean_box(0);
v_a_830_ = lean_array_uget_borrowed(v_as_814_, v_i_816_);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_828_, v___f_825_, v___x_829_, v_a_830_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; 
lean_dec_ref_known(v___x_831_, 1);
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_add(v_i_816_, v___x_833_);
v_i_816_ = v___x_834_;
v_b_817_ = v___x_832_;
goto _start;
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_a_813_);
v_a_836_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_831_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___boxed(lean_object* v___x_844_, lean_object* v_a_845_, lean_object* v_as_846_, lean_object* v_sz_847_, lean_object* v_i_848_, lean_object* v_b_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_11245__boxed_853_; size_t v_sz_boxed_854_; size_t v_i_boxed_855_; lean_object* v_res_856_; 
v___x_11245__boxed_853_ = lean_unbox(v___x_844_);
v_sz_boxed_854_ = lean_unbox_usize(v_sz_847_);
lean_dec(v_sz_847_);
v_i_boxed_855_ = lean_unbox_usize(v_i_848_);
lean_dec(v_i_848_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_11245__boxed_853_, v_a_845_, v_as_846_, v_sz_boxed_854_, v_i_boxed_855_, v_b_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v_as_846_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(uint8_t v___x_857_, lean_object* v_a_858_, lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec(v_a_858_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_b_862_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_876_; 
lean_dec_ref(v_b_862_);
v___x_868_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_869_ = lean_box(0);
v___f_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_871_ = lean_box(v___x_857_);
v___x_872_ = lean_box(v___x_866_);
lean_inc(v_a_858_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_873_, 0, v___x_868_);
lean_closure_set(v___f_873_, 1, v___x_871_);
lean_closure_set(v___f_873_, 2, v_a_858_);
lean_closure_set(v___f_873_, 3, v___x_869_);
lean_closure_set(v___f_873_, 4, v___x_872_);
v___x_874_ = lean_box(0);
v_a_875_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
lean_inc(v_a_875_);
v___x_876_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_873_, v___f_870_, v___x_874_, v_a_875_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
lean_dec_ref_known(v___x_876_, 1);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__1));
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_861_, v___x_878_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19(v___x_857_, v_a_858_, v_as_859_, v_sz_860_, v___x_879_, v___x_877_, v___y_863_, v___y_864_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_858_);
v_a_881_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_876_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___boxed(lean_object* v___x_889_, lean_object* v_a_890_, lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v___x_11315__boxed_898_; size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v___x_11315__boxed_898_ = lean_unbox(v___x_889_);
v_sz_boxed_899_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_900_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_11315__boxed_898_, v_a_890_, v_as_891_, v_sz_boxed_899_, v_i_boxed_900_, v_b_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_as_891_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(uint8_t v___x_905_, lean_object* v_a_906_, lean_object* v_as_907_, size_t v_sz_908_, size_t v_i_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_a_906_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_910_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_924_; 
lean_dec_ref(v_b_910_);
v___x_916_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_917_ = lean_box(0);
v___f_918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_919_ = lean_box(v___x_905_);
v___x_920_ = lean_box(v___x_914_);
lean_inc(v_a_906_);
v___f_921_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_921_, 0, v___x_916_);
lean_closure_set(v___f_921_, 1, v___x_919_);
lean_closure_set(v___f_921_, 2, v_a_906_);
lean_closure_set(v___f_921_, 3, v___x_917_);
lean_closure_set(v___f_921_, 4, v___x_920_);
v___x_922_ = lean_box(0);
v_a_923_ = lean_array_uget_borrowed(v_as_907_, v_i_909_);
lean_inc(v_a_923_);
v___x_924_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_921_, v___f_918_, v___x_922_, v_a_923_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; 
lean_dec_ref_known(v___x_924_, 1);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_909_, v___x_926_);
v_i_909_ = v___x_927_;
v_b_910_ = v___x_925_;
goto _start;
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_906_);
v_a_929_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_924_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___boxed(lean_object* v___x_937_, lean_object* v_a_938_, lean_object* v_as_939_, lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v___x_11383__boxed_946_; size_t v_sz_boxed_947_; size_t v_i_boxed_948_; lean_object* v_res_949_; 
v___x_11383__boxed_946_ = lean_unbox(v___x_937_);
v_sz_boxed_947_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_948_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_11383__boxed_946_, v_a_938_, v_as_939_, v_sz_boxed_947_, v_i_boxed_948_, v_b_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_as_939_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(uint8_t v___x_950_, lean_object* v_a_951_, lean_object* v_as_952_, size_t v_sz_953_, size_t v_i_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_usize_dec_lt(v_i_954_, v_sz_953_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v_a_951_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_955_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v___x_969_; 
lean_dec_ref(v_b_955_);
v___x_961_ = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_2377040249____hygCtx___hyg_9_;
v___x_962_ = lean_box(0);
v___f_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13_spec__19___closed__0));
v___x_964_ = lean_box(v___x_950_);
v___x_965_ = lean_box(v___x_959_);
lean_inc(v_a_951_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13___lam__1___boxed), 11, 5);
lean_closure_set(v___f_966_, 0, v___x_961_);
lean_closure_set(v___f_966_, 1, v___x_964_);
lean_closure_set(v___f_966_, 2, v_a_951_);
lean_closure_set(v___f_966_, 3, v___x_962_);
lean_closure_set(v___f_966_, 4, v___x_965_);
v___x_967_ = lean_box(0);
v_a_968_ = lean_array_uget_borrowed(v_as_952_, v_i_954_);
lean_inc(v_a_968_);
v___x_969_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7(v___f_966_, v___f_963_, v___x_967_, v_a_968_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
lean_dec_ref_known(v___x_969_, 1);
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18___closed__0));
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_add(v_i_954_, v___x_971_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17_spec__18(v___x_950_, v_a_951_, v_as_952_, v_sz_953_, v___x_972_, v___x_970_, v___y_956_, v___y_957_);
return v___x_973_;
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_a_951_);
v_a_974_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_969_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_969_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17___boxed(lean_object* v___x_982_, lean_object* v_a_983_, lean_object* v_as_984_, lean_object* v_sz_985_, lean_object* v_i_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_11451__boxed_991_; size_t v_sz_boxed_992_; size_t v_i_boxed_993_; lean_object* v_res_994_; 
v___x_11451__boxed_991_ = lean_unbox(v___x_982_);
v_sz_boxed_992_ = lean_unbox_usize(v_sz_985_);
lean_dec(v_sz_985_);
v_i_boxed_993_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_11451__boxed_991_, v_a_983_, v_as_984_, v_sz_boxed_992_, v_i_boxed_993_, v_b_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_as_984_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(lean_object* v_init_995_, uint8_t v___x_996_, lean_object* v_a_997_, lean_object* v_n_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
if (lean_obj_tag(v_n_998_) == 0)
{
lean_object* v_cs_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; size_t v_sz_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v_cs_1003_ = lean_ctor_get(v_n_998_, 0);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_b_999_);
v_sz_1006_ = lean_array_size(v_cs_1003_);
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_995_, v___x_996_, v_a_997_, v_cs_1003_, v_sz_1006_, v___x_1007_, v___x_1005_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1023_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1023_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1023_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_fst_1013_; 
v_fst_1013_ = lean_ctor_get(v_a_1009_, 0);
if (lean_obj_tag(v_fst_1013_) == 0)
{
lean_object* v_snd_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v_snd_1014_ = lean_ctor_get(v_a_1009_, 1);
lean_inc(v_snd_1014_);
lean_dec(v_a_1009_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_snd_1014_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1015_);
v___x_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v_val_1019_; lean_object* v___x_1021_; 
lean_inc_ref(v_fst_1013_);
lean_dec(v_a_1009_);
v_val_1019_ = lean_ctor_get(v_fst_1013_, 0);
lean_inc(v_val_1019_);
lean_dec_ref_known(v_fst_1013_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_val_1019_);
v___x_1021_ = v___x_1011_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_val_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1008_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1008_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_vs_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v_vs_1032_ = lean_ctor_get(v_n_998_, 0);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_b_999_);
v_sz_1035_ = lean_array_size(v_vs_1032_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__17(v___x_996_, v_a_997_, v_vs_1032_, v_sz_1035_, v___x_1036_, v___x_1034_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1052_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_fst_1042_; 
v_fst_1042_ = lean_ctor_get(v_a_1038_, 0);
if (lean_obj_tag(v_fst_1042_) == 0)
{
lean_object* v_snd_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v_snd_1043_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_snd_1043_);
lean_dec(v_a_1038_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_snd_1043_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1050_; 
lean_inc_ref(v_fst_1042_);
lean_dec(v_a_1038_);
v_val_1048_ = lean_ctor_get(v_fst_1042_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_fst_1042_, 1);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_val_1048_);
v___x_1050_ = v___x_1040_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1037_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1037_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(lean_object* v_init_1061_, uint8_t v___x_1062_, lean_object* v_a_1063_, lean_object* v_as_1064_, size_t v_sz_1065_, size_t v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1066_, v_sz_1065_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_a_1063_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_b_1067_);
return v___x_1072_;
}
else
{
lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1107_; 
v_snd_1073_ = lean_ctor_get(v_b_1067_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_b_1067_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_b_1067_, 0);
lean_dec(v_unused_1108_);
v___x_1075_ = v_b_1067_;
v_isShared_1076_ = v_isSharedCheck_1107_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_dec(v_b_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1107_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v_a_1078_ = lean_array_uget_borrowed(v_as_1064_, v_i_1066_);
lean_inc(v_snd_1073_);
lean_inc(v_a_1063_);
v___x_1079_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1061_, v___x_1062_, v_a_1063_, v_a_1078_, v_snd_1073_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1098_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1098_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1098_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_a_1080_) == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec(v_a_1063_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1080_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1084_);
v___x_1086_ = v___x_1075_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1073_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; 
lean_del_object(v___x_1082_);
lean_dec(v_snd_1073_);
v_a_1091_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_a_1080_, 1);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_a_1091_);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1093_ = v___x_1075_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1091_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
size_t v___x_1094_; size_t v___x_1095_; 
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_add(v_i_1066_, v___x_1094_);
v_i_1066_ = v___x_1095_;
v_b_1067_ = v___x_1093_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_del_object(v___x_1075_);
lean_dec(v_snd_1073_);
lean_dec(v_a_1063_);
v_a_1099_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1079_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1079_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16___boxed(lean_object* v_init_1109_, lean_object* v___x_1110_, lean_object* v_a_1111_, lean_object* v_as_1112_, lean_object* v_sz_1113_, lean_object* v_i_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v___x_11511__boxed_1119_; size_t v_sz_boxed_1120_; size_t v_i_boxed_1121_; lean_object* v_res_1122_; 
v___x_11511__boxed_1119_ = lean_unbox(v___x_1110_);
v_sz_boxed_1120_ = lean_unbox_usize(v_sz_1113_);
lean_dec(v_sz_1113_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_res_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12_spec__16(v_init_1109_, v___x_11511__boxed_1119_, v_a_1111_, v_as_1112_, v_sz_boxed_1120_, v_i_boxed_1121_, v_b_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v_as_1112_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12___boxed(lean_object* v_init_1123_, lean_object* v___x_1124_, lean_object* v_a_1125_, lean_object* v_n_1126_, lean_object* v_b_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v___x_11532__boxed_1131_; lean_object* v_res_1132_; 
v___x_11532__boxed_1131_ = lean_unbox(v___x_1124_);
v_res_1132_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1123_, v___x_11532__boxed_1131_, v_a_1125_, v_n_1126_, v_b_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_n_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(uint8_t v___x_1133_, lean_object* v_a_1134_, lean_object* v_t_1135_, lean_object* v_init_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_root_1140_; lean_object* v_tail_1141_; lean_object* v___x_1142_; 
v_root_1140_ = lean_ctor_get(v_t_1135_, 0);
v_tail_1141_ = lean_ctor_get(v_t_1135_, 1);
lean_inc(v_a_1134_);
v___x_1142_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__12(v_init_1136_, v___x_1133_, v_a_1134_, v_root_1140_, v_init_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1179_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1179_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1179_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
if (lean_obj_tag(v_a_1143_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; 
lean_dec(v_a_1134_);
v_a_1147_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v_a_1143_, 1);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_a_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; size_t v_sz_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1145_);
v_a_1151_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v_a_1143_, 1);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1151_);
v_sz_1154_ = lean_array_size(v_tail_1141_);
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8_spec__13(v___x_1133_, v_a_1134_, v_tail_1141_, v_sz_1154_, v___x_1155_, v___x_1153_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1170_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; 
v_fst_1161_ = lean_ctor_get(v_a_1157_, 0);
if (lean_obj_tag(v_fst_1161_) == 0)
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; 
v_snd_1162_ = lean_ctor_get(v_a_1157_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_snd_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_snd_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; 
lean_inc_ref(v_fst_1161_);
lean_dec(v_a_1157_);
v_val_1166_ = lean_ctor_get(v_fst_1161_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_fst_1161_, 1);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_val_1166_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_val_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1156_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1156_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1134_);
v_a_1180_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1142_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1142_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8___boxed(lean_object* v___x_1188_, lean_object* v_a_1189_, lean_object* v_t_1190_, lean_object* v_init_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___x_11718__boxed_1195_; lean_object* v_res_1196_; 
v___x_11718__boxed_1195_ = lean_unbox(v___x_1188_);
v_res_1196_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_11718__boxed_1195_, v_a_1189_, v_t_1190_, v_init_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_t_1190_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(lean_object* v_o_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_env_1202_; lean_object* v___x_1203_; lean_object* v_toEnvExtension_1204_; lean_object* v_asyncMode_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v_merged_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v___x_1200_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1201_ = lean_st_ref_get(v___y_1198_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v___x_1203_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1204_ = lean_ctor_get(v___x_1203_, 0);
v_asyncMode_1205_ = lean_ctor_get(v_toEnvExtension_1204_, 2);
v___x_1206_ = lean_box(0);
v___x_1207_ = 0;
v___x_1208_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1200_, v___x_1203_, v_env_1202_, v_asyncMode_1205_, v___x_1206_, v___x_1207_);
v_merged_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1218_);
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_merged_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v_merged_1209_);
lean_ctor_set(v___x_1211_, 0, v_o_1197_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_o_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_merged_1209_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1219_, v___y_1220_);
lean_dec(v___y_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_scopes_1228_; lean_object* v___x_1229_; lean_object* v_opts_1230_; lean_object* v___x_1231_; 
v___x_1226_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1227_ = lean_st_ref_get(v___y_1224_);
v_scopes_1228_ = lean_ctor_get(v___x_1227_, 2);
lean_inc(v_scopes_1228_);
lean_dec(v___x_1227_);
v___x_1229_ = l_List_head_x21___redArg(v___x_1226_, v_scopes_1228_);
lean_dec(v_scopes_1228_);
v_opts_1230_ = lean_ctor_get(v___x_1229_, 1);
lean_inc_ref(v_opts_1230_);
lean_dec(v___x_1229_);
v___x_1231_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_opts_1230_, v___y_1224_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1___boxed(lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0(lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1240_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1238_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1(v___y_1237_, v___y_1238_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = l_Lean_Linter_Coe_linter_deprecatedCoercions;
v___x_1245_ = l_Lean_Linter_getLinterValue(v___x_1244_, v_a_1243_);
lean_dec(v_a_1243_);
v___x_1246_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Coe_coeLinter_spec__2___redArg(v___y_1238_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Coe_coeLinter_spec__8(v___x_1245_, v_a_1241_, v_a_1247_, v___x_1248_, v___y_1237_, v___y_1238_);
lean_dec(v_a_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1257_);
v___x_1251_ = v___x_1249_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1248_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Coe_coeLinter___lam__0___boxed(lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Linter_Coe_coeLinter___lam__0(v_x_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_x_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(lean_object* v_o_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___redArg(v_o_1274_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1___boxed(lean_object* v_o_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Coe_coeLinter_spec__1_spec__1(v_o_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(uint8_t v___x_1284_, lean_object* v_i_1285_, lean_object* v_a_1286_, lean_object* v_as_1287_, lean_object* v_as_x27_1288_, lean_object* v_b_1289_, lean_object* v_a_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___redArg(v___x_1284_, v_i_1285_, v_a_1286_, v_as_x27_1288_, v_b_1289_, v___y_1291_, v___y_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6___boxed(lean_object* v___x_1295_, lean_object* v_i_1296_, lean_object* v_a_1297_, lean_object* v_as_1298_, lean_object* v_as_x27_1299_, lean_object* v_b_1300_, lean_object* v_a_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v___x_11971__boxed_1305_; lean_object* v_res_1306_; 
v___x_11971__boxed_1305_ = lean_unbox(v___x_1295_);
v_res_1306_ = l_List_forIn_x27_loop___at___00Lean_Linter_Coe_coeLinter_spec__6(v___x_11971__boxed_1305_, v_i_1296_, v_a_1297_, v_as_1298_, v_as_x27_1299_, v_b_1300_, v_a_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v_as_x27_1299_);
lean_dec(v_as_1298_);
lean_dec(v_a_1297_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(lean_object* v_msgData_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___redArg(v_msgData_1307_, v___y_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_Coe_coeLinter_spec__5_spec__7_spec__8(v_msgData_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___redArg(v_msg_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__12(v_00_u03b1_1323_, v_msg_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(lean_object* v_00_u03b1_1329_, lean_object* v_preNode_1330_, lean_object* v_postNode_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___redArg(v_preNode_1330_, v_postNode_1331_, v_x_1332_, v_x_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_preNode_1339_, lean_object* v_postNode_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10(v_00_u03b1_1338_, v_preNode_1339_, v_postNode_1340_, v_x_1341_, v_x_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1347_, lean_object* v_preNode_1348_, lean_object* v_postNode_1349_, lean_object* v___x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___redArg(v_preNode_1348_, v_postNode_1349_, v___x_1350_, v_x_1351_, v_x_1352_, v___y_1353_, v___y_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_preNode_1358_, lean_object* v_postNode_1359_, lean_object* v___x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_Coe_coeLinter_spec__7_spec__10_spec__13(v_00_u03b1_1357_, v_preNode_1358_, v_postNode_1359_, v___x_1360_, v_x_1361_, v_x_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Linter_Coe_coeLinter));
v___x_1369_ = l_Lean_Elab_Command_addLinter(v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2____boxed(lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_Linter_Coe_0__Lean_Linter_Coe_initFn_00___x40_Lean_Linter_Coe_650813316____hygCtx___hyg_2_();
return v_res_1371_;
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
